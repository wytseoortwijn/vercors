package vct.silver;

import viper.api.*;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Properties;
import java.util.Set;
import java.util.TreeMap;

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
  
  
  public static <T,E,S,DFunc,DAxiom,Program>
  ViperAPI<Origin,VerificationError,T,E,S,DFunc,DAxiom,Program>
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
      Constructor[] constructors = v_class.getConstructors();
      if (constructors.length!=1) {
        throw new HREError("class had %d constructors instead of 1",constructors.length);
      }
      obj=constructors[0].newInstance(new HREOrigins());
    } catch(Exception e) {
      e.printStackTrace();
      throw new HREError("Exception %s",e);
    }
    if (!(obj instanceof ViperAPI)){
      hre.System.Fail("Plugin is incompatible: cannot cast verifier.");
    }
    @SuppressWarnings("unchecked")
    ViperAPI<Origin,VerificationError,T,E,S,DFunc,DAxiom,Program> verifier=(ViperAPI<Origin, VerificationError, T, E, S, DFunc, DAxiom, Program>)obj;
    //verifier.set_tool_home(Configuration.getToolHome());
    return verifier;
  }
  
  public static <T,E,S,Decl,DFunc,DAxiom,Program>
  TestReport TestSilicon(ProgramUnit arg, String tool) {
    //hre.System.Output("verifying with %s backend",silver_module.get());
    long start_time=System.currentTimeMillis();
    ViperAPI<Origin,VerificationError,T,E,S,DFunc,DAxiom,Program> verifier=getVerifier(tool);
    //verifier.set_detail(Configuration.detailed_errors.get());
    VerCorsViperAPI vercors=VerCorsViperAPI.get();
    Program program=vercors.prog.convert(verifier,arg);
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
    ViperControl control=new ViperControl();
    try {
      HashSet<Origin> reachable=new HashSet();
      List<? extends ViperError<Origin>> errs=verifier.verify(
          Configuration.getToolHome(),settings,program,reachable,control);
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
      HashSet<Origin> accounted=new HashSet();
      for(String method:control.verified_methods){
        for(Origin o:vercors.refuted.get(method)){
          if(!reachable.contains(o)){
            o.report("error","statement is not reachable");
            report.setVerdict(Verdict.Fail);
          } else {
            accounted.add(o);
          }
        }
      }
      for(Origin o:reachable){
        if (!accounted.contains(o)){
          System.err.printf("unregistered location %s marked reachable%n",o);
        }
      }
    } catch (Exception e){
      e.printStackTrace();
      report.setVerdict(Verdict.Error);
    } finally {
      control.done();
    }
    end_time=System.currentTimeMillis();
    System.err.printf("verification took %d ms%n", end_time-start_time);
    return report;
  }

  protected static <T, E, S, Program> void split_block(
      ExpressionFactory<Origin,T, E> verifier,
      SilverTypeMap<T> type, SilverStatementMap<T, E, S> stat,
      List<Triple<Origin,String,T>> locals, BlockStatement block, ArrayList<S> stats)
      throws HREError {
    int i=0;
    int N=block.getLength();
    while(i<N && (block.get(i) instanceof DeclarationStatement)){
      DeclarationStatement decl=(DeclarationStatement)block.get(i);
      locals.add(new Triple(decl.getOrigin(),decl.getName(),decl.getType().apply(type)));
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
