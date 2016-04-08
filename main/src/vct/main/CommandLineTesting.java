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
    TestcaseVisitor tv=new TestcaseVisitor();
    for(String dir:selftest){
      if (dir.equals("")){
        System.err.println("Testing backends.");
        res=runtest(tt,Verdict.Inconclusive,"z3","-smt2","//examples/backends/test-sat.smt");
        res.mustSay("p true");
        res.mustSay("q true");
        check(res,"z3","sat");

        res=runtest(tt,Verdict.Inconclusive,"z3","-smt2","//examples/backends/test-unsat.smt");  
        res.mustSay("unsat");
        check(res,"z3","unsat");

        res=runtest(tt,Verdict.Inconclusive,"boogie","//examples/backends/test-pass.bpl");  
        res.mustSay("Boogie program verifier finished with 1 verified, 0 errors");
        check(res,"boogie","passing");

        res = runtest(tt,Verdict.Inconclusive,"boogie","//examples/backends/test-fail.bpl");
        res.mustSay("Boogie program verifier finished with 0 verified, 1 error");
        check(res,"boogie","failing");
        
        res=runtest(tt,Verdict.Inconclusive,"chalice","//examples/backends/test-pass.chalice");  
        res.mustSay("Boogie program verifier finished with 3 verified, 0 errors");
        check(res,"chalice","passing");
        
        res=runtest(tt,Verdict.Inconclusive,"chalice","//examples/backends/test-fail.chalice");  
        res.mustSay("Boogie program verifier finished with 2 verified, 1 error");
        check(res,"chalice","failing");
        
        res=runtest(tt,Verdict.Inconclusive,"dafny","/compile:0","//examples/backends/test-pass.dfy");  
        res.mustSay("Dafny program verifier finished with 2 verified, 0 errors");
        check(res,"dafny","passing");
        
        res=runtest(tt,Verdict.Error,"dafny","/compile:0","//examples/backends/test-fail.dfy");  
        res.mustSay("Dafny program verifier finished with 1 verified, 1 error");
        check(res,"dafny","failing");
        
        res=runtest(tt,Verdict.Inconclusive,"carbon","//examples/backends/test-pass.sil");  
        res.mustSay("No errors found.");
        check(res,"carbon","passing");
        
        res=runtest(tt,Verdict.Error,"carbon","//examples/backends/test-fail.sil");  
        res.mustSay("Assignment might fail. Divisor 0 might be zero.");
        check(res,"carbon","failing");

        res=runtest(tt,Verdict.Inconclusive,"silicon","//examples/backends/test-pass.sil");  
        res.mustSay("No errors found.");
        check(res,"silicon","passing");

        res=runtest(tt,Verdict.Error,"silicon","//examples/backends/test-fail.sil");  
        res.mustSay("Assignment might fail. Divisor 0 might be zero.");
        check(res,"silicon","failing");

        continue;
      }
      try {
        Files.walkFileTree(Paths.get(dir),tv);
      } catch (IOException e) {
        e.printStackTrace();
      }
    }
    if (tv.delayed_fail) System.exit(1);
    int successes=0;
    HashMap<String,Testcase> untested=new HashMap<String,Testcase>();
    HashMap<String,String> failures=new HashMap<String, String>();
    for(Entry<String,Testcase> item:tv.testsuite.entrySet()){
      String name=item.getKey();
      Testcase test=item.getValue();
      if (test.tools.isEmpty()){
        untested.put(name,test);
      }
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
        for(Path f:test.files) cmd.add(f.toAbsolutePath().toString());
        System.err.printf("running %s/%s:%n",name,tool);
        for(String s:cmd){
          System.err.printf(" %s",s);
        }
        System.err.printf("%n");
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
    if (!untested.isEmpty()){
      System.err.printf("The following %d tests have been disabled:%n",untested.size());
      for(Entry<String,Testcase> item:untested.entrySet()){
        String name=item.getKey();
        Testcase test=item.getValue();
        System.err.printf("  %s ",name);
        String sep="(";
        for(Path f:test.files) {
          System.err.printf("%s%s",sep,f.toString());
          sep=" ";
        }
        System.err.printf(")%n");
      }
    }
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
      System.err.printf("there were %d unmarked files:%n",tv.unmarked.size());
      for(Path p: tv.unmarked){
        System.err.printf("  %s%n",p);
      }
    }
    if(pass){
      System.exit(0);
    } else {
      System.exit(1);
    }
  }

  private static void check(VCTResult res,String tool,String test) {
    if (res.verdict !=Verdict.Pass) {
      System.err.printf("%s did not pass the %s test%s",tool,test);
      System.exit(1);
    }
  }

  private static VCTResult runtest(ToolTest tt,Verdict expect,String ... args) {
    System.err.printf("executing");
    for(String s:args) System.err.printf(" %s",s);
    System.err.println();
    VCTResult res;
    res=tt.run(args);  
    if (res.verdict==expect){
      res.verdict=Verdict.Pass;
    } else {
      System.err.printf("%s did not execute properly%n",args[0]);
      System.exit(1);
    }
    return res;
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
