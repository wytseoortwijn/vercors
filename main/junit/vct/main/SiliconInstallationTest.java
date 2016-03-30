package vct.main;

import hre.util.TestReport.Verdict;
import org.junit.Test;
import org.junit.runner.RunWith;
import com.google.code.tempusfugit.concurrency.ConcurrentTestRunner;
import static vct.main.Feature.*;

public class SiliconInstallationTest extends ToolTest {

  @Test
  public void testZ3sat(){
      VCTResult res=run("z3","-smt2","//examples/backends/test-sat.smt");  
      res.mustSay("sat");
  }
  
  @Test
  public void testZ3unsat(){
      VCTResult res=run("z3","-smt2","//examples/backends/test-unsat.smt");  
      res.mustSay("sat");
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
   
  @Test
  public void testHistoryProcessesPVL(){
      VCTResult res=run("vct","--silver=silicon","--check-defined","//examples/histories/History.pvl");
      res.checkVerdict(Verdict.Pass);
  }
  
  @Test
  public void testHistoryLemmasPVL(){
      VCTResult res=run("vct","--silver=silicon","--check-axioms","//examples/histories/History.pvl");
      res.checkVerdict(Verdict.Pass);
  }
  
  @Test
  public void testHistoryApplication(){
      VCTResult res=run("vct","--silver=silicon","--check-history",
          "//examples/histories/History.pvl","//examples/histories/HistoryApplication.java");
      res.checkVerdict(Verdict.Pass);
  }
  
  @Test
  public void testThreadInheritance(){
      VCTResult res=run("vct","--silver=silicon",
          "//examples/threads/SpecifiedThread.java",
          "//examples/threads/Worker.java",
          "//examples/threads/VerifiedMain.java"
          );
      res.checkVerdict(Verdict.Pass);
  }

  @Test
  public void testThreadInheritanceE1(){
      VCTResult res=run("vct","--silver=silicon",
          "//examples/threads/SpecifiedThread.java",
          "//examples/threads/Worker.java",
          "//examples/threads/VerifiedMain-E1.java"
          );
      res.checkVerdict(Verdict.Fail);
  }

  @Test
  public void testThreadInheritanceE2(){
      VCTResult res=run("vct","--silver=silicon",
          "//examples/threads/SpecifiedThread.java",
          "//examples/threads/Worker.java",
          "//examples/threads/VerifiedMain-E2.java"
          );
      res.checkVerdict(Verdict.Fail);
  }

  @Test
  public void testThreadInheritanceReal(){
      VCTResult res=run("vct","--silver=silicon",
          "//examples/threads/SpecifiedThread.java",
          "//examples/threads/Worker.java",
          "//examples/threads/Main.java"
          );
      res.checkVerdict(Verdict.Pass);
  }
  
  @Test
  public void testGoto1err(){
      VCTResult res=run("vct","--silver=silicon","//examples/goto/goto1.pvl");
      res.checkVerdict(Verdict.Fail);
  }

  @Test
  public void testGoto2(){
      VCTResult res=run("vct","--silver=silicon","//examples/goto/goto2.pvl");
      res.checkVerdict(Verdict.Pass);
  }
  
  @Test
  public void testValue1err(){
      VCTResult res=run("vct","--silver=silicon","//examples/technical/test-value1.java");
      res.checkVerdict(Verdict.Fail);
  }
  
  @Test
  public void testValue2err(){
      VCTResult res=run("vct","--silver=silicon","//examples/technical/test-value2.java");
      res.checkVerdict(Verdict.Fail);
  }

  @Test
  public void testCollections(){
      VCTResult res=run("vct","--silver=silicon","//examples/basic/CollectionTest.pvl");
      res.checkVerdict(Verdict.Pass);
  }

}
