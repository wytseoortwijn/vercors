package vct.main;

import static org.junit.Assert.*;
import hre.util.TestReport.Verdict;

import java.security.Permission;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;

import org.junit.Test;
import org.junit.runner.RunWith;

import sun.applet.Main;

import com.google.code.tempusfugit.concurrency.ConcurrentTestRunner;

@RunWith(ConcurrentTestRunner.class) 
public class VerifastTest extends ToolTest {
  
  @Test
  public void testOutputBinderPVL(){
    sem_get();
    try {
      VCTResult res=run("vct","--verifast","//pvl_examples/outputbinder.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testOutputBinderPVLerr1(){
    sem_get();
    try {
      VCTResult res=run("vct","--verifast","//pvl_examples/outputbinder-e1.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

}
