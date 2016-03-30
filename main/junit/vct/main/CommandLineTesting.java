package vct.main;

import java.util.ArrayList;
import java.util.HashMap;
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

public class CommandLineTesting {
  
  public static boolean enabled(){
    return append_option.used();
  }
  
  private static Map<String,Class<?>> testmap=new LinkedHashMap<String, Class<?>>();
  static {
    testmap.put("backend",vct.main.DependencyTest.class);
    testmap.put("manual",vct.main.ManualTest.class);
    testmap.put("main",vct.main.MainTest.class);
    testmap.put("silicon",vct.main.SiliconInstallationTest.class);
    testmap.put("silicon-apps",vct.main.SiliconApplicationTest.class);
    testmap.put("dafny",vct.main.DafnyTest.class);
    testmap.put("verifast",vct.main.VerifastTest.class);
    testmap.put("refute",vct.main.RefuteTest.class);
    testmap.put("carp",vct.main.CARPTestExamples.class);
  }
  
  public static void run_testsuites(){
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
  }
  
  private static StringListSetting selftest=new StringListSetting();
  private static Option append_option;
  protected static StringSetting savedir=new StringSetting(null);
  
  public static void add_options(OptionParser clops) {
    append_option=selftest.getAppendOption("execute test suites from the command line. "+
        "Valid test suites are: "+testmap.keySet());
    clops.add(append_option,"test");
    clops.add(savedir.getAssign("save intermediate files to given directory"),"save-intermediate");
  }

}
