// -*- tab-width:2 ; indent-tabs-mode:nil -*-

package vct.main;

import hre.ast.MessageOrigin;
import hre.config.BooleanSetting;
import hre.config.OptionParser;
import hre.config.StringListSetting;
import hre.debug.HeapDump;
import hre.io.PrefixPrintStream;
import hre.util.CompositeReport;
import hre.util.TestReport;

import java.io.*;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;
import java.util.Map.Entry;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import vct.col.annotate.DeriveModifies;
import vct.col.ast.*;
import vct.col.rewrite.AssignmentRewriter;
import vct.col.rewrite.ConstructorRewriter;
import vct.col.rewrite.DefineDouble;
import vct.col.rewrite.ExplicitPermissionEncoding;
import vct.col.rewrite.FilterClass;
import vct.col.rewrite.FinalizeArguments;
import vct.col.rewrite.Flatten;
import vct.col.rewrite.ForallRule;
import vct.col.rewrite.GlobalizeStaticsField;
import vct.col.rewrite.GlobalizeStaticsParameter;
import vct.col.rewrite.GuardedCallExpander;
import vct.col.rewrite.InheritanceRewriter;
import vct.col.rewrite.ReorderAssignments;
import vct.col.rewrite.ResolveAndMerge;
import vct.col.rewrite.ReferenceEncoding;
import vct.col.rewrite.SimplifyCalls;
import vct.col.rewrite.StripConstructors;
import vct.col.rewrite.VoidCalls;
import vct.col.util.FeatureScanner;
import vct.col.util.SimpleTypeCheck;
import vct.util.ClassName;
import vct.util.Configuration;
import static hre.System.*;
import static hre.ast.Context.globalContext;

class Main
{  
  private static ProgramUnit program=new ProgramUnit();
  
  private static void parseFile(String name){
    int dot=name.lastIndexOf('.');
    if (dot<0) {
      Fail("cannot deduce language of %s",name);
    }
    String lang=name.substring(dot+1);
    if (lang.equals("pvl")){
      //TODO: fix this kludge.
      vct.col.ast.ASTNode.pvl_mode=true;
    }
    Progress("Parsing %s file %s",lang,name);
    ProgramUnit unit=Parser.parse(lang,name);
    program.merge(unit);
    Progress("Read %s succesfully",name);
  }

  private static List<ClassName> classes;
  
  static class ChaliceTask implements Callable<TestReport> {
    private ClassName class_name;
    private ProgramUnit program;

    public ChaliceTask(ProgramUnit program,ClassName class_name){
      this.program=program;
      this.class_name=class_name;
    }
    @Override
    public TestReport call() {
      System.err.printf("Validating class %s...%n",class_name.toString("."));
      long start=System.currentTimeMillis();
      ProgramUnit task=new FilterClass(program,class_name.name).rewriteAll();
      task=new ResolveAndMerge(task).rewriteAll();
      new SimpleTypeCheck(task).check();
      TestReport report=vct.boogie.Main.TestChalice(task);
      System.err.printf("%s: result is %s (%dms)%n",class_name.toString("."),
          report.getVerdict(),System.currentTimeMillis()-start);
      return report;
    }
    
  }

  public static void main(String[] args) throws Throwable
  {
    OptionParser clops=new OptionParser();
    clops.add(clops.getHelpOption(),'h',"help");

    BooleanSetting boogie=new BooleanSetting(false);
    clops.add(boogie.getEnable("select Boogie backend"),"boogie");
    BooleanSetting chalice=new BooleanSetting(false);
    clops.add(chalice.getEnable("select Chalice backend"),"chalice");
    final BooleanSetting separate_checks=new BooleanSetting(false);
    clops.add(separate_checks.getEnable("validate classes separately"),"separate");
    BooleanSetting help_passes=new BooleanSetting(false);
    clops.add(help_passes.getEnable("print help on available passes"),"help-passes");
    BooleanSetting hoare_check=new BooleanSetting(false);
    clops.add(hoare_check.getEnable("select Hoare Logic Checker backend"),"hlc");
    StringListSetting pass_list=new StringListSetting();
    clops.add(pass_list.getAppendOption("add to the custom list of compilation passes"),"passes");
    StringListSetting show_before=new StringListSetting();
    clops.add(show_before.getAppendOption("Show source code before given passes"),"show-before");
    StringListSetting show_after=new StringListSetting();
    clops.add(show_after.getAppendOption("Show source code after given passes"),"show-after");
   
    BooleanSetting explicit_encoding=new BooleanSetting(false);
    clops.add(explicit_encoding.getEnable("explicit encoding"),"explicit");
    BooleanSetting apply_forall_rule=new BooleanSetting(false);
    clops.add(apply_forall_rule.getEnable("apply forall rule"),"apply-forall");
    BooleanSetting reference_encoding=new BooleanSetting(false);
    clops.add(reference_encoding.getEnable("reference encoding"),"refenc");
    BooleanSetting global_with_field=new BooleanSetting(false);
    clops.add(global_with_field.getEnable("Encode global access with a field rather than a parameter. (expert option)"),"global-with-field");
    
    BooleanSetting infer_modifies=new BooleanSetting(false);
    clops.add(infer_modifies.getEnable("infer modifies clauses"),"infer-modifies");
    BooleanSetting no_context=new BooleanSetting(false);
    clops.add(no_context.getEnable("disable printing the context of errors"),"no-context");
    
    StringListSetting debug_list=new StringListSetting();
    clops.add(debug_list.getAppendOption("print debug message for given classes and/or packages"),"debug");
    
    BooleanSetting progress=new BooleanSetting(false);
    clops.add(progress.getEnable("print progress messages"),"progress");
    Configuration.add_options(clops);
    
    String input[]=clops.parse(args);
    hre.System.setProgressReporting(progress.get());
    
    for(String name:debug_list){
      hre.System.EnableDebug(name,java.lang.System.err,"vct("+name+")");
    }

    Hashtable<String,CompilerPass> defined_passes=new Hashtable<String,CompilerPass>();
    Hashtable<String,ValidationPass> defined_checks=new Hashtable<String,ValidationPass>();
    defined_passes.put("java",new CompilerPass("print AST in java syntax"){
      public ProgramUnit apply(ProgramUnit arg){
        vct.java.printer.JavaPrinter.dump(System.out,arg);
        return arg;
      }
    });
    defined_passes.put("dump",new CompilerPass("dump AST"){
      public ProgramUnit apply(ProgramUnit arg){
        PrefixPrintStream out=new PrefixPrintStream(System.out);
        HeapDump.tree_dump(out,arg,ASTNode.class);
        return arg;
      }
    });
    defined_passes.put("assign",new CompilerPass("change inline assignments to statements"){
      public ProgramUnit apply(ProgramUnit arg){
        return new AssignmentRewriter(arg).rewriteAll();
      }
    });
    defined_checks.put("boogie",new ValidationPass("verify with Boogie"){
      public TestReport apply(ProgramUnit arg){
        return vct.boogie.Main.TestBoogie(arg);
      }
    });
    defined_checks.put("chalice",new ValidationPass("verify with Chalice"){
      public TestReport apply(ProgramUnit arg){
        if (separate_checks.get()) {
          long start=System.currentTimeMillis();
          CompositeReport res=new CompositeReport();
          ExecutorService queue=Executors.newFixedThreadPool(4);
          ArrayList<Future<TestReport>> list=new ArrayList<Future<TestReport>>();
          for(ClassName class_name:arg.classNames()){
              Callable<TestReport> task=new ChaliceTask(arg,class_name);
              System.err.printf("submitting verification of %s%n",class_name.toString("."));
              list.add(queue.submit(task));
          }
          queue.shutdown();
          for(Future<TestReport> future:list){
            try {
              res.addReport(future.get());
            } catch (InterruptedException e) {
              // TODO Auto-generated catch block
              e.printStackTrace();
              Abort("%s",e);
            } catch (ExecutionException e) {
              // TODO Auto-generated catch block
              e.printStackTrace();
              Abort("%s",e);
            }
          }
          System.err.printf("verification took %dms%n", System.currentTimeMillis()-start);
          return res;
        } else {
          long start=System.currentTimeMillis();
          TestReport report=vct.boogie.Main.TestChalice(arg);
          System.err.printf("verification took %dms%n", System.currentTimeMillis()-start);
          return report;
        }
      }
    });
    defined_passes.put("check",new CompilerPass("run a type check"){
      public ProgramUnit apply(ProgramUnit arg){
        new SimpleTypeCheck(arg).check();
        return arg;
      }
    });
    defined_passes.put("define_double",new CompilerPass("Rewrite double as a non-native data type."){
      public ProgramUnit apply(ProgramUnit arg){
        return DefineDouble.rewrite(arg);
      }
    });
    defined_passes.put("expand",new CompilerPass("expand guarded method calls"){
      public ProgramUnit apply(ProgramUnit arg){
        return new GuardedCallExpander(arg).rewriteAll();
      }
    });
    defined_passes.put("explicit_encoding",new CompilerPass("encode required and ensured permission as ghost arguments"){
      public ProgramUnit apply(ProgramUnit arg){
        return new ExplicitPermissionEncoding(arg).rewriteAll();
      }
    });
    defined_passes.put("finalize_args",new CompilerPass("???"){
      public ProgramUnit apply(ProgramUnit arg){
        return new FinalizeArguments(arg).rewriteAll();
      }
    });
    defined_passes.put("flatten",new CompilerPass("remove nesting of expression"){
      public ProgramUnit apply(ProgramUnit arg){
        return new Flatten(arg).rewriteAll();
      }
    });
    defined_passes.put("forall_rule",new CompilerPass("Apply the forall rule to predicates"){
      public ProgramUnit apply(ProgramUnit arg){
        return new ForallRule(arg).rewriteAll();
      }
    });
    if (global_with_field.get()){
      Warning("Using the incomplete and experimental field access for globals.");
      defined_passes.put("globalize",new CompilerPass("split classes into static and dynamic parts"){
        public ProgramUnit apply(ProgramUnit arg){
          return new GlobalizeStaticsField(arg).rewriteAll();
        }
      });      
    } else {
      defined_passes.put("globalize",new CompilerPass("split classes into static and dynamic parts"){
        public ProgramUnit apply(ProgramUnit arg){
          return new GlobalizeStaticsParameter(arg).rewriteAll();
        }
      });
    }
    defined_checks.put("hoare_logic",new ValidationPass("Check Hoare Logic Proofs"){
      public TestReport apply(ProgramUnit arg){
        for(ASTClass cl:arg.classes()){
          Brain.main(cl);
        }
        return null;
      }
    });
    defined_passes.put("inheritance",new CompilerPass("rewrite contract to reflect inheritance"){
      public ProgramUnit apply(ProgramUnit arg){
        return new InheritanceRewriter(arg).rewriteOrdered();
      }
    });
    defined_passes.put("modifies",new CompilerPass("Derive modifies clauses for all contracts"){
      public ProgramUnit apply(ProgramUnit arg){
        new DeriveModifies().annotate(arg);
        return arg;
      }
    });
    defined_passes.put("reorder",new CompilerPass("reorder statements (e.g. all declarations at the start of a bock"){
      public ProgramUnit apply(ProgramUnit arg){
        return new ReorderAssignments(arg).rewriteAll();
      }
    });
    defined_passes.put("refenc",new CompilerPass("apply reference encoding"){
      public ProgramUnit apply(ProgramUnit arg){
        return new ReferenceEncoding(arg).rewriteAll();
      }
    });
    defined_passes.put("resolv",new CompilerPass("resolv all names"){
      public ProgramUnit apply(ProgramUnit arg){
        return new ResolveAndMerge(arg).rewriteAll();
      }
    });
    defined_passes.put("rm_cons",new CompilerPass("???"){
      public ProgramUnit apply(ProgramUnit arg){
        return new ConstructorRewriter(arg).rewriteAll();
      }
    });
    defined_passes.put("simplify_calls",new CompilerPass("???"){
      public ProgramUnit apply(ProgramUnit arg){
        return new SimplifyCalls(arg).rewriteAll();
      }
    });
    defined_passes.put("strip_constructors",new CompilerPass("Strip constructors from classes"){
      public ProgramUnit apply(ProgramUnit arg){
        return new StripConstructors(arg).rewriteAll();
      }
    });
    defined_passes.put("voidcalls",new CompilerPass("???"){
      public ProgramUnit apply(ProgramUnit arg){
        return new VoidCalls(arg).rewriteAll();
      }
    });
    if (help_passes.get()) {
      System.out.println("The following passes are available:"); 
      for (Entry<String, CompilerPass> entry:defined_passes.entrySet()){
        System.out.printf(" %-12s : %s%n",entry.getKey(),entry.getValue().getDescripion());
      }
      for (Entry<String, ValidationPass> entry:defined_checks.entrySet()){
        System.out.printf(" %-12s : %s%n",entry.getKey(),entry.getValue().getDescripion());
      }
      System.exit(0);
    }
    if (!(boogie.get() || chalice.get() || hoare_check.get() || pass_list.iterator().hasNext())) {
      Fail("no back-end or passes specified");
    }
    Progress("parsing inputs...");
    int cnt = 0;
    long startTime = System.currentTimeMillis();
    for(String name : input){
      File f=new File(name);
      if (!no_context.get()){
        globalContext.add(name);
      }
      parseFile(f.getPath());
      cnt++;
    }
    Progress("Parsed %d files in: %dms",cnt,System.currentTimeMillis() - startTime);
    startTime = System.currentTimeMillis();
    program=new ResolveAndMerge(program).rewriteAll();
    new SimpleTypeCheck(program).check();
    Progress("Initial type check took %dms",System.currentTimeMillis() - startTime);
    FeatureScanner features=new FeatureScanner();
    program.accept(features);
    classes=new ArrayList();
    for (ClassName name:program.classNames()){
      classes.add(name);
    }
    List<String> passes=null;
    if (boogie.get()) {
    	passes=new ArrayList<String>();
      passes.add("flatten");
      passes.add("assign");
      passes.add("finalize_args");
      passes.add("reorder");
      passes.add("simplify_calls");
      if (infer_modifies.get()) {
        passes.add("resolv");
        passes.add("check");
        passes.add("modifies");
      }
      passes.add("resolv");
      passes.add("check");
      passes.add("voidcalls");
      passes.add("resolv");
      passes.add("check");
      passes.add("flatten");
      passes.add("resolv");
      passes.add("check");
      passes.add("strip_constructors");
      passes.add("resolv");
      passes.add("check");
    	passes.add("boogie");
    } else if (chalice.get()) {
    	passes=new ArrayList<String>();
      if (apply_forall_rule.get()){
        passes.add("forall_rule");
        passes.add("resolv");
        passes.add("check");       
      }
      if (features.hasStaticItems()){
        Warning("Encoding globals by means of an argument.");
        passes.add("globalize");
        passes.add("resolv");
        passes.add("check");
      }
      if (features.usesInheritance()){
        passes.add("inheritance");
        passes.add("resolv");
        passes.add("check");       
      }
      if (explicit_encoding.get()){
        passes.add("expand");
        passes.add("resolv");
        passes.add("check");
        passes.add("explicit_encoding");
        passes.add("resolv");
        passes.add("check");
      }
      passes.add("flatten");
      passes.add("resolv");
      passes.add("check");
      if (reference_encoding.get()){
        passes.add("refenc");
        passes.add("resolv");
        passes.add("check");
      }
      if (features.usesDoubles()){
        Warning("defining Double");
        passes.add("define_double");
        passes.add("resolv");
        passes.add("check");
      }
    	passes.add("assign");
      passes.add("reorder");
    	passes.add("expand");
    	passes.add("resolv");
    	passes.add("check");
      passes.add("rm_cons");
      passes.add("resolv");
      passes.add("check");
      passes.add("voidcalls");
      passes.add("resolv");
      passes.add("check");
      passes.add("flatten");
      passes.add("resolv");
      passes.add("check");
    	passes.add("chalice");
    } else if (hoare_check.get()) {
    	passes=new ArrayList<String>();
    	passes.add("resolv");
    	passes.add("assign");
    	passes.add("hoare_logic");
    } else {
    	if (!pass_list.iterator().hasNext()) Abort("no back-end or passes specified");
    }
    {
      TestReport res=null;
      for(String pass:passes!=null?passes:pass_list){
        if (res!=null){
          Progress("Ignoring intermediate verdict %s",res.getVerdict());
          res=null;
        }
        CompilerPass task=defined_passes.get(pass);
        if (show_before.contains(pass)){
          vct.java.printer.JavaPrinter.dump(System.out,program);
        }
        if (task!=null){
          Progress("Applying %s ...", pass);
          startTime = System.currentTimeMillis();
          program=task.apply(program);
          Progress(" ... pass took %d ms",System.currentTimeMillis()-startTime);
        } else {
          ValidationPass check=defined_checks.get(pass);
          if (check!=null){
            Progress("Applying %s ...", pass);
            startTime = System.currentTimeMillis();
            res=check.apply(program);
            Progress(" ... pass took %d ms",System.currentTimeMillis()-startTime);
          } else {
            Fail("unknown pass %s",pass);
          }
        }
        if (show_after.contains(pass)){
          vct.java.printer.JavaPrinter.dump(System.out,program);
        }
      }
      if (res!=null) {
        Output("The final verdict is %s",res.getVerdict());
      } else {
        Fail("No overall verdict has been set. Check the output carefully!");
      }
    }
  }
}

