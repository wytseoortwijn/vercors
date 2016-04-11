package vct.silver;

import viper.api.*;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Properties;

import hre.HREError;
import hre.ast.Origin;
import hre.config.IntegerSetting;
import hre.config.StringSetting;
import hre.io.Container;
import hre.io.DirContainer;
import hre.io.JarContainer;
import hre.io.UnionContainer;
import hre.util.ContainerClassLoader;
import hre.util.TestReport;
import hre.util.TestReport.Verdict;
import vct.col.ast.*;
import vct.col.util.ASTUtils;
import vct.error.VerificationError;
import vct.util.Configuration;

public class SilverBackend {
  
  public static StringSetting silver_module=new StringSetting(null);
  public static IntegerSetting silicon_z3_timeout=new IntegerSetting(30000);
  
  
  public static <T,E,S,Decl,DFunc,DAxiom,Program>
  SilverVerifier<Origin,VerificationError,T,E,S,Decl,DFunc,DAxiom,Program>
  getVerifier(String tool){
    boolean parser=tool.equals("parser");
    if (parser){
      tool="silicon";
    } else {
      hre.System.Output("verifying with %s %s backend",
          silver_module.used()?silver_module.get():"builtin",tool);
    }
    File jarfile;
    if (silver_module.used()){
      jarfile=Configuration.getToolHome().resolve(silver_module.get()+"/"+tool+".jar").toFile();
    } else {
      jarfile=Configuration.getHome().resolve("viper/"+tool+"/target/scala-2.11/"+tool+".jar").toFile();
    }
    //System.err.printf("adding jar %s to path%n",jarfile);
    Container container;
    if (silver_module.used()){
      container=new JarContainer(jarfile);
    } else {
      File classdir1=Configuration.getHome().resolve("viper/silver/target/scala-2.11/classes").toFile();
      File classdir2=Configuration.getHome().resolve("viper/"+tool+"/target/scala-2.11/classes").toFile();
      container=new UnionContainer(
          new DirContainer(classdir1),
          new DirContainer(classdir2),
          new JarContainer(jarfile));
    }
    Object obj;
    //TODO: Properties silver_props=new Properties();
    //TODO: Properties verifier_props=new Properties();
    try {
      ClassLoader loader=new ContainerClassLoader(container);
      //TODO: InputStream is=loader.getResourceAsStream("silver.hglog");
      //TODO: silver_props.load(is);
      //TODO: is.close();
      //TODO: System.err.printf("silver properties: %s%n", silver_props);
      //TODO: is=loader.getResourceAsStream("verifier.hglog");
      //TODO: verifier_props.load(is);
      //TODO: is.close();
      //TODO: System.err.printf("verifier properties: %s%n", verifier_props);
      Class<?> v_class;
      if (parser) {
        v_class=loader.loadClass("viper.api.SilverImplementation");
      } else if (tool.contains("silicon")){
        v_class=loader.loadClass("viper.api.SiliconVerifier");
      } else if (tool.contains("carbon")) {
        v_class=loader.loadClass("viper.api.CarbonVerifier");
      } else {
        throw new HREError("cannot guess the main class of %s",tool);
      }
      obj=v_class.newInstance();
    } catch(Exception e) {
      e.printStackTrace();
      throw new HREError("Exception %s",e);
    }
    if (!(obj instanceof SilverVerifier)){
      hre.System.Fail("Plugin is incompatible: cannot cast verifier.");
    }
    @SuppressWarnings("unchecked")
    SilverVerifier<Origin,VerificationError,T,E,S,Decl,DFunc,DAxiom,Program> verifier=(SilverVerifier<Origin, VerificationError, T, E, S, Decl, DFunc, DAxiom, Program>)obj;
    verifier.set_tool_home(Configuration.getToolHome());
    return verifier;
  }
  
  public static <T,E,S,Decl,DFunc,DAxiom,Program>
  TestReport TestSilicon(ProgramUnit arg, String tool) {
    //hre.System.Output("verifying with %s backend",silver_module.get());
    long start_time=System.currentTimeMillis();
    SilverVerifier<Origin,VerificationError,T,E,S,Decl,DFunc,DAxiom,Program> verifier=getVerifier(tool);
    verifier.set_detail(Configuration.detailed_errors.get());
    SilverTypeMap<T> type=new SilverTypeMap<T>(verifier);
    SilverExpressionMap<T, E, Decl> expr=new SilverExpressionMap<T,E,Decl>(verifier,type);
    SilverStatementMap<T, E, S, Decl> stat=new SilverStatementMap<T,E,S,Decl>(verifier,type,expr);
    Program program=verifier.program();
    for(ASTNode entry:arg) {
      if (entry instanceof Method) {
        Method m = (Method)entry;
        switch(m.kind){
        case Plain:{
          ArrayList<Decl> in=new ArrayList<Decl>();
          ArrayList<Decl> out=new ArrayList<Decl>();
          for(DeclarationStatement decl:m.getArgs()){
            Decl d=verifier.decl(decl.getOrigin(),decl.getName(),decl.getType().apply(type));
            if (decl.isValidFlag(ASTFlags.OUT_ARG) && decl.getFlag(ASTFlags.OUT_ARG)){
              out.add(d);
            } else {
              in.add(d);
            }
          }
          ArrayList<Decl> locals=new ArrayList<Decl>();
          S body;
          if (m.getBody() instanceof BlockStatement){
            BlockStatement block=(BlockStatement)m.getBody();
            ArrayList<S> stats=new ArrayList<S>();
            split_block(verifier, type, stat, locals, block, stats);
            body=verifier.block(block.getOrigin(),stats);
          } else if (m.getBody()==null){
            Origin o=m.getOrigin();
            ArrayList<S> l=new ArrayList<S>();
            l.add(verifier.inhale(o,verifier.Constant(o, false)));
            body=verifier.block(o,l);
          } else {
            throw new HREError("unexpected body %s",Configuration.getDiagSyntax().print(m.getBody()));
          }
          ArrayList<E> pres=new ArrayList<E>();
          ArrayList<E> posts=new ArrayList<E>();
          Contract c=m.getContract();
          if (c!=null){
            for(ASTNode n:ASTUtils.conjuncts(c.pre_condition,StandardOperator.Star)){
              pres.add(n.apply(expr));
            }
            for(ASTNode n:ASTUtils.conjuncts(c.post_condition,StandardOperator.Star)){
              posts.add(n.apply(expr));
            }
          }
          verifier.add_method(program,m.getOrigin(),m.name,pres,posts,in,out,locals,body);
          break;
        }
        case Pure:{
          ArrayList<Decl> args=new ArrayList<Decl>();
          for(DeclarationStatement decl:m.getArgs()){
            Decl d=verifier.decl(decl.getOrigin(),decl.getName(),decl.getType().apply(type));
            args.add(d);
          }
          T t=m.getReturnType().apply(type);
          ArrayList<E> pres=new ArrayList<E>();
          ArrayList<E> posts=new ArrayList<E>();
          Contract c=m.getContract();
          if (c!=null){
            for(ASTNode n:ASTUtils.conjuncts(c.pre_condition,StandardOperator.Star)){
              pres.add(n.apply(expr));
            }
            for(ASTNode n:ASTUtils.conjuncts(c.post_condition,StandardOperator.Star)){
              posts.add(n.apply(expr));
            }
          }
          ASTNode b=m.getBody();
          E body=(b==null?null:b.apply(expr));
          verifier.add_function(program,m.getOrigin(),m.name,args,t,pres,posts,body);
          break;
        }
        case Predicate:{
          ASTNode b=m.getBody();
          E body=(b==null?null:b.apply(expr));
          ArrayList<Decl> args=new ArrayList<Decl>();
          for(DeclarationStatement decl:m.getArgs()){
            Decl d=verifier.decl(decl.getOrigin(),decl.getName(),decl.getType().apply(type));
            args.add(d);
          }
          verifier.add_predicate(program,m.getOrigin(),m.name,args,body);
          break;
        }
        default:
          throw new HREError("method kind %s not supported",m.kind);
        }
      } else if (entry instanceof ASTClass){
        ASTClass cl=(ASTClass) entry;
        if (cl.name.equals("Ref")&& cl.kind==ASTClass.ClassKind.Record){
          for(DeclarationStatement decl:cl.dynamicFields()){
            verifier.add_field(program, decl.getOrigin(), decl.getName(), decl.getType().apply(type));
          }
        } else {
          throw new HREError("bad class entry: %s",cl.name);
        }
      } else if (entry instanceof AxiomaticDataType) {
        AxiomaticDataType adt=(AxiomaticDataType)entry;
        ArrayList<DFunc> funcs=new ArrayList<DFunc>();
        for(Method m:adt.constructors()){
          ArrayList<Decl> args=new ArrayList<Decl>();
          for(DeclarationStatement decl:m.getArgs()){
            Decl d=verifier.decl(decl.getOrigin(),decl.getName(),decl.getType().apply(type));
            args.add(d);
          }
          funcs.add(verifier.dfunc(m.getOrigin(),m.name, args,m.getReturnType().apply(type),adt.name));
        }
        for(Method m:adt.mappings()){
          ArrayList<Decl> args=new ArrayList<Decl>();
          for(DeclarationStatement decl:m.getArgs()){
            Decl d=verifier.decl(decl.getOrigin(),decl.getName(),decl.getType().apply(type));
            args.add(d);
          }
          funcs.add(verifier.dfunc(m.getOrigin(),m.name, args,m.getReturnType().apply(type),adt.name));
        }
        ArrayList<DAxiom> axioms=new ArrayList<DAxiom>();
        for(Axiom axiom:adt.axioms()){
          axioms.add(verifier.daxiom(axiom.getOrigin(),axiom.name,axiom.getRule().apply(expr),adt.name));
        }
        ArrayList<String> pars=new ArrayList<String>();
        for(DeclarationStatement decl:adt.getParameters()){
          pars.add(decl.getName());
        }
        verifier.add_adt(program,adt.getOrigin(),adt.name,funcs,axioms,pars);
      } else if(entry instanceof ASTSpecialDeclaration){
        ASTSpecialDeclaration s=(ASTSpecialDeclaration)entry;
        switch(s.kind){
          case Comment:
            // comments are not supported in silver.
            continue;
          default:
            throw new HREError("bad special declaration entry: %s",s.kind);

        }
      } else {
        throw new HREError("bad entry: %s",entry.getClass());
      }
    }
    long end_time=System.currentTimeMillis();
    System.err.printf("Backend AST conversion took %d ms%n", end_time-start_time);
    String fname=vct.util.Configuration.backend_file.get();
    if (fname!=null){
      PrintWriter pw=null;
      try {
         pw = new java.io.PrintWriter(new java.io.File(fname));
         verifier.write_program(pw,program);
      } catch (FileNotFoundException e) {
        e.printStackTrace();
      } finally {
        if (pw!=null) pw.close();
      }
    }

    Properties settings=new Properties();
    if (tool.startsWith("silicon")){
      //settings.setProperty("smt.soft_timeout",silicon_z3_timeout.get()+"");
    }
    TestReport report=new TestReport();
    start_time=System.currentTimeMillis();
    try {
      HashSet<Origin> reachable=new HashSet();
      List<? extends ViperError<Origin>> errs=verifier.verify(Configuration.getToolHome(),settings,program,reachable);
      for(Origin o:reachable){
        if (!stat.refuted.contains(o)){
          System.err.printf("unregistered location %s marked reachable%n",o);
        }
      }
      if (errs.size()>0){
        for(ViperError<Origin> e:errs){
          int N=e.getExtraCount();
          for(int i=0;i<N;i++){
            Origin o=(Origin)e.getOrigin(i);
            String msg=e.getError(i);
            if (o==null){
              System.err.printf("unknown location: %s%n", msg);
            } else {
              o.report("error",msg);
            }
          }
        }
        report.setVerdict(Verdict.Fail);
      } else {
        report.setVerdict(Verdict.Pass);
      }
      for(Origin o:stat.refuted){
        if(!reachable.contains(o)){
          o.report("error","statement is not reachable");
          report.setVerdict(Verdict.Fail);
        }
      }
    } catch (Exception e){
      e.printStackTrace();
      report.setVerdict(Verdict.Error);
    }
    end_time=System.currentTimeMillis();
    System.err.printf("verification took %d ms%n", end_time-start_time);
    return report;
  }

  protected static <T, E, S, Decl, Program> void split_block(
      SilverVerifier<Origin, ?, T, E, S, Decl, ?, ? , Program> verifier,
      SilverTypeMap<T> type, SilverStatementMap<T, E, S, Decl> stat,
      ArrayList<Decl> locals, BlockStatement block, ArrayList<S> stats)
      throws HREError {
    int i=0;
    int N=block.getLength();
    while(i<N && (block.get(i) instanceof DeclarationStatement)){
      DeclarationStatement decl=(DeclarationStatement)block.get(i);
      locals.add(verifier.decl(decl.getOrigin(),decl.getName(),decl.getType().apply(type)));
      i=i+1;
    }
    for(;i<N;i++){
      if (block.get(i) instanceof DeclarationStatement) {
        throw new HREError("illegal declaration");
      }
      S s=block.get(i).apply(stat);
      if (s!=null){
        stats.add(s);
      }
    }
  }

}
