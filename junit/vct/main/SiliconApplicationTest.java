package vct.main;

import hre.util.TestReport.Verdict;
import org.junit.Test;
import org.junit.runner.RunWith;
import com.google.code.tempusfugit.concurrency.ConcurrentTestRunner;

@RunWith(ConcurrentTestRunner.class) 
public class SiliconApplicationTest extends ToolTest {
  
  @Test
  public void testZeroArray(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//examples/silicon/zero-array-ic.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testZeroArrayE1(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//examples/silicon/zero-array-ic-e1.c");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testDepParLoop(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//examples/silicon/dep-par-loop.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testDepParLoopE1(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//examples/silicon/dep-par-loop-e1.c");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testLoopInvariant(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//examples/silicon/LoopInvariant.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testLoopInvariantE1(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//examples/silicon/LoopInvariant-e1.c");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

}
