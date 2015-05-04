package vct.main;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

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
    testmap.put("silicon",vct.main.SiliconApplicationTest.class);
    testmap.put("dafny",vct.main.DafnyTest.class);
    testmap.put("verifast",vct.main.VerifastTest.class);
    testmap.put("refute",vct.main.RefuteTest.class);
  }
  
  public static void run_testsuites(){
    JUnitCore junit = new JUnitCore();
    Iterable<String> collection;
    if (selftest.contains("*")){
      collection=testmap.keySet();
    } else {
      collection=selftest;
    }
    for(String suite:collection){
      Class<?> cls=testmap.get(suite);
      if (cls==null) {
        System.err.printf("unknown test suite %s%n",suite);
        System.err.printf("valid test suties are: %s%n",testmap.keySet());
        System.exit(1);
      }
      System.err.printf("Running %s.%n",cls);
      Result result = junit.run(cls);
      int E=result.getFailureCount();
      System.err.printf("==============================================%n");
      System.err.printf("While running %s: %d failures out of %d tests%n",cls,E,result.getRunCount());
      if (E>0){
        System.err.printf("----------------------------------------------%n");
        System.err.printf("The following tests failed:%n");
        for (Failure f:result.getFailures()){
          System.err.printf("%s%n",f.getDescription());
        }
      }
      System.err.printf("==============================================%n");
      if (E>0) {
        System.err.printf("test suite %s failed.%n",suite);
        System.exit(1);
      }
    }
    System.err.printf("all test suites have been succesful.%n");
    System.exit(0);
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
