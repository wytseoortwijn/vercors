package vct.main;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.junit.runner.JUnitCore;
import org.junit.runner.Result;
import org.junit.runner.notification.Failure;

import hre.config.Option;
import hre.config.OptionParser;
import hre.config.StringListSetting;
import hre.config.StringSetting;
import hre.util.TestReport.Verdict;

import java.io.BufferedInputStream;


public class CommandLineTesting {
  
 
  public static boolean enabled(){
    return append_option.used();
  }
  
  public static void run_testsuites(){
    ToolTest tt=new ToolTest();
    VCTResult res;
    res=tt.run("z3","-smt2","//examples/backends/test-sat.smt");
    if (res.verdict==Verdict.Inconclusive){
      res.verdict=Verdict.Pass;
    } else {
      System.err.println("Z3 did not execute properly");
      System.exit(1);
    }
    res.mustSay("p true");
    res.mustSay("q true");
    if (res.verdict !=Verdict.Pass) {
      System.err.println("Z3 did not conclude sat");
      System.exit(1);
    }
    res=tt.run("z3","-smt2","//examples/backends/test-unsat.smt");  
    if (res.verdict==Verdict.Inconclusive){
      res.verdict=Verdict.Pass;
    } else {
      System.err.println("Z3 did not execute properly");
      System.exit(1);
    }
    res.mustSay("unsat");
    if (res.verdict !=Verdict.Pass) {
      System.err.println("Z3 did not conclude unsat");
      System.exit(1);
    }
    res=tt.run("boogie","//examples/backends/test-pass.bpl");  
    if (res.verdict==Verdict.Inconclusive){
      res.verdict=Verdict.Pass;
    } else {
      System.err.println("Boogie did not execute properly");
      System.exit(1);
    }
    res.mustSay("Boogie program verifier finished with 1 verified, 0 errors");
    if (res.verdict !=Verdict.Pass) {
      System.err.println("Boogie did not pass the passing test");
      System.exit(1);
    }
    res=tt.run("boogie","//examples/backends/test-fail.bpl");  
    if (res.verdict==Verdict.Inconclusive){
      res.verdict=Verdict.Pass;
    } else {
      System.err.println("Boogie did not execute properly");
      System.exit(1);
    }
    res.mustSay("Boogie program verifier finished with 0 verified, 1 error");
    if (res.verdict !=Verdict.Pass) {
      System.err.println("Boogie did not pass the failing test");
      System.exit(1);
    }
   
/* 
  @Test
  public void testChalicePass(){
      VCTResult res=run("chalice","//examples/backends/test-pass.chalice");  
      res.mustSay("Boogie program verifier finished with 3 verified, 0 errors");
  }

  @Test
  public void testChaliceFail(){
      VCTResult res=run("chalice","//examples/backends/test-fail.chalice");  
      res.mustSay("Boogie program verifier finished with 2 verified, 1 error");
  }
  
  @Test
  public void testCarbonPass(){
      VCTResult res=run("carbon","//examples/backends/test-pass.sil");  
      res.mustSay("No errors found.");
  }

  @Test
  public void testCarbonFail(){
      VCTResult res=run("carbon","//examples/backends/test-fail.sil");  
      res.mustSay("Assignment might fail. Divisor 0 might be zero.");
  }

  
  @Test
  public void testSiliconPass(){
      VCTResult res=run("silicon","//examples/backends/test-pass.sil");  
      res.mustSay("No errors found.");
  }

  @Test
  public void testSiliconFail(){
      VCTResult res=run("silicon","//examples/backends/test-fail.sil");  
      res.mustSay("Assignment might fail. Divisor 0 might be zero.");
  }

}
*/
    TestcaseVisitor tv=new TestcaseVisitor();
    for(String dir:selftest){
      try {
        Files.walkFileTree(Paths.get(dir).toAbsolutePath(),tv);
      } catch (IOException e) {
        e.printStackTrace();
      }
    }
    int successes=0;
    HashMap<String,String> failures=new HashMap<String, String>();
    for(Entry<String,Testcase> item:tv.testsuite.entrySet()){
      String name=item.getKey();
      Testcase test=item.getValue();
      for(String tool:test.tools){
        ArrayList<String> cmd=new ArrayList<String>();
        cmd.add("vct");
        switch(tool){
        case "silicon":
        case "carbon":
          cmd.add("--silver="+tool);
          break;
        default:
          cmd.add("--"+tool);
        }
        for(String opt:test.options) cmd.add(opt);
        for(Path f:test.files) cmd.add(f.toString());
        System.err.printf("running %s/%s%n",name,tool);
        res=tt.run(cmd.toArray(new String[0]));
        System.err.printf("finished %s/%s: %s/%s %n",name,tool,res.verdict,test.verdict);
        if (res.verdict.toString().equals(test.verdict)){
          successes++;
        } else {
          failures.put(name+"/"+tool,String.format(
              "verdict is %s instead of %s",res.verdict,test.verdict));
        }
      }
    }
    boolean pass=true;
    if(failures.isEmpty()){
      System.err.printf("all %d tests passed%n",successes);
    } else {
      pass=false;
      System.err.printf("the following tests failed%n");
      for(Entry<String,String> t:failures.entrySet()){
        System.err.printf("  %s: %s%n",t.getKey(),t.getValue());
      }
      System.err.printf("total %s successes and %d failures%n",successes,failures.size());
    }
    if (tv.unmarked.size()>0){
      pass=false;
      System.err.printf("there were %d unmarked files%n",tv.unmarked.size());
    }
    if(pass){
      System.exit(0);
    } else {
      System.exit(1);
    }
    
    /*
    JUnitCore junit = new JUnitCore();
    Iterable<String> collection;
    if (selftest.contains("*")){
      collection=testmap.keySet();
    } else {
      collection=selftest;
    }
    HashMap<String,Result> list=new HashMap();
    for(String suite:collection){ // check if all tests are valid.
      Class<?> cls=testmap.get(suite);
      if (cls==null) {
        System.err.printf("unknown test suite %s%n",suite);
        System.err.printf("valid test suties are: %s%n",testmap.keySet());
        System.exit(1);
      }
    }
    for(String suite:collection){ // run all the valid tests.
      Class<?> cls=testmap.get(suite);
      System.err.printf("Running %s.%n",cls);
      Result result = junit.run(cls);
      list.put(cls.toString(),result);
    }
    boolean OK=true;
    for(Entry<String,Result> e:list.entrySet()){
      String name=e.getKey();
      Result result=e.getValue();
      int E=result.getFailureCount();
      System.err.printf("==============================================%n");
      System.err.printf("While running %s: %d failures out of %d tests%n",name,E,result.getRunCount());
      if (E>0){
        System.err.printf("----------------------------------------------%n");
        System.err.printf("The following tests failed:%n");
        for (Failure f:result.getFailures()){
          System.err.printf("%s%n",f.getDescription());
        }
      }
      if (E>0) OK=false;
    }
    System.err.printf("==============================================%n");
    if (OK){
      System.err.printf("all test suites have been succesful.%n");
      System.exit(0);
    } else {
      System.err.printf("one or more test suites failed.%n");
      System.exit(1);
    }
    */
  }
  
  private static StringListSetting selftest=new StringListSetting();
  private static Option append_option;
  protected static StringSetting savedir=new StringSetting(null);
  
  public static void add_options(OptionParser clops) {
    append_option=selftest.getAppendOption("execute test suites from the command line. "+
        "Each test suite is a folder which is scanned for valid test inputs");
    clops.add(append_option,"test");
    clops.add(savedir.getAssign("save intermediate files to given directory"),"save-intermediate");
  }

}
