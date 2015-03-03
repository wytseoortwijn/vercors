package vct.silver;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import hre.HREError;
import hre.ast.Origin;
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
  
  public static StringSetting silver_module=new StringSetting("silver/latest");;
  public static <T,E,S,Decl,DFunc,DAxiom,Program>
  TestReport TestSilicon(ProgramUnit arg, String tool) {
    long start_time=System.currentTimeMillis();
    File jarfile=Configuration.getToolHome().resolve(silver_module.get()+"/"+tool+".jar").toFile();
    System.err.printf("adding jar %s to path%n",jarfile);
    JarContainer container=new JarContainer(jarfile);
    Object obj;
    Properties silver_props=new Properties();
    Properties verifier_props=new Properties();
    try {
      ClassLoader loader=new ContainerClassLoader(container);
      InputStream is=loader.getResourceAsStream("silver.hglog");
      silver_props.load(is);
      is.close();
      System.err.printf("silver properties: %s%n", silver_props);
      is=loader.getResourceAsStream("verifier.hglog");
      verifier_props.load(is);
      is.close();
      System.err.printf("verifier properties: %s%n", verifier_props);
      Class v_class;
      if (tool.contains("silicon")){
        v_class=loader.loadClass("vct.silver.SiliconVerifier");
      } else if (tool.contains("carbon")) {
        v_class=loader.loadClass("vct.silver.CarbonVerifier");
      } else {
        throw new HREError("cannot guess the main class of %s",tool);
      }
      obj=v_class.newInstance();
    } catch(Exception e) {
      e.printStackTrace();
      TestReport res=new TestReport();
      res.setException(e);
      return res;
    }
    SilverVerifier<Origin,VerificationError,T,E,S,Decl,DFunc,DAxiom,Program> verifier=new WrappedSilverVerifier(obj);
    SilverTypeMap<T> type=new SilverTypeMap(verifier);
    SilverExpressionMap<T, E, Decl> expr=new SilverExpressionMap(verifier,type);
    SilverStatementMap<T, E, S, Decl> stat=new SilverStatementMap(verifier,type,expr);
    Program program=verifier.program();
    for(ASTNode entry:arg) {
      if (entry instanceof Method) {
        Method m = (Method)entry;
        switch(m.kind){
        case Plain:{
          hre.System.Warning("plain method %s",m.name);
          
          ArrayList<Decl> in=new ArrayList();
          ArrayList<Decl> out=new ArrayList();
          for(DeclarationStatement decl:m.getArgs()){
            Decl d=verifier.decl(decl.getOrigin(),decl.getName(),decl.getType().apply(type));
            if (decl.isValidFlag(ASTFlags.OUT_ARG) && decl.getFlag(ASTFlags.OUT_ARG)){
              out.add(d);
            } else {
              in.add(d);
            }
          }
          ArrayList<Decl> locals=new ArrayList();
          S body;
          if (m.getBody() instanceof BlockStatement){
            BlockStatement block=(BlockStatement)m.getBody();
            ArrayList<S> stats=new ArrayList();
            split_block(verifier, type, stat, locals, block, stats);
            body=verifier.block(block.getOrigin(),stats);
          } else {
            body=m.getBody().apply(stat);
          }
          ArrayList<E> pres=new ArrayList();
          ArrayList<E> posts=new ArrayList();
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
          ArrayList<Decl> args=new ArrayList();
          for(DeclarationStatement decl:m.getArgs()){
            Decl d=verifier.decl(decl.getOrigin(),decl.getName(),decl.getType().apply(type));
            args.add(d);
          }
          T t=m.getReturnType().apply(type);
          ArrayList<E> pres=new ArrayList();
          ArrayList<E> posts=new ArrayList();
          Contract c=m.getContract();
          if (c!=null){
            for(ASTNode n:ASTUtils.conjuncts(c.pre_condition,StandardOperator.Star)){
              pres.add(n.apply(expr));
            }
            for(ASTNode n:ASTUtils.conjuncts(c.post_condition,StandardOperator.Star)){
              posts.add(n.apply(expr));
            }
          }
          E body=m.getBody().apply(expr);
          verifier.add_function(program,m.getOrigin(),m.name,args,t,pres,posts,body);
          break;
        }
        case Predicate:{
          E body=m.getBody().apply(expr);
          ArrayList<Decl> args=new ArrayList();
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
        ArrayList<DFunc> funcs=new ArrayList();
        for(Method m:adt.constructors()){
          ArrayList<Decl> args=new ArrayList();
          for(DeclarationStatement decl:m.getArgs()){
            Decl d=verifier.decl(decl.getOrigin(),decl.getName(),decl.getType().apply(type));
            args.add(d);
          }
          funcs.add(verifier.dfunc(m.getOrigin(),m.name, args,m.getReturnType().apply(type)));
        }
        for(Method m:adt.mappings()){
          ArrayList<Decl> args=new ArrayList();
          for(DeclarationStatement decl:m.getArgs()){
            Decl d=verifier.decl(decl.getOrigin(),decl.getName(),decl.getType().apply(type));
            args.add(d);
          }
          funcs.add(verifier.dfunc(m.getOrigin(),m.name, args,m.getReturnType().apply(type)));
        }
        ArrayList<DAxiom> axioms=new ArrayList();
        for(Axiom axiom:adt.axioms()){
          axioms.add(verifier.daxiom(axiom.getOrigin(),axiom.name,axiom.getRule().apply(expr)));
        }
        ArrayList<String> pars=new ArrayList();
        for(DeclarationStatement decl:adt.getParameters()){
          pars.add(decl.getName());
        }
        verifier.add_adt(program,adt.getOrigin(),adt.name,funcs,axioms,pars);
      } else {
        throw new HREError("bad entry: %s",entry.getClass());
      }
    }
    long end_time=System.currentTimeMillis();
    System.err.printf("AST conversion took %d ms%n", end_time-start_time);
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

    TestReport report=new TestReport();
    start_time=System.currentTimeMillis();
    try {
      List<VerificationError> errs=verifier.verify(new ErrorFactory(),Configuration.getToolHome(),program);
      if (errs.size()>0){
        report.setVerdict(Verdict.Fail);
      } else {
        report.setVerdict(Verdict.Pass);
      }
    } catch (Exception e){
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
      stats.add(block.get(i).apply(stat));
    }
  }

}
