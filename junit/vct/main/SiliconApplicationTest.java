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
      VCTResult res=run("vct","--silver=silicon_qp",
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
      VCTResult res=run("vct","--silver=silicon_qp",
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
      VCTResult res=run("vct","--silver=silicon_qp",
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
      VCTResult res=run("vct","--silver=silicon_qp",
          "//examples/silicon/dep-par-loop-e1.c");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testDepParLoopBack(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp",
          "//examples/silicon/dep-par-loop-back.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testDepParLoopBackE1(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp",
          "//examples/silicon/dep-par-loop-back-e1.c");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testLoopInvariant(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/silicon/LoopInvariant.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testLoopInvariantE1(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/silicon/LoopInvariant-e1.c");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testNestedDoubleIC(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/silicon/ZeroArrayNested.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testNestedSingleIC(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/silicon/ZeroArrayNestedSingle.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testZeroMatrix(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/silicon/zero-matrix.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  // type error!
  public void testSumArray(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/silicon/SumArray.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  // type error!
  public void testSumArrayErr1(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/silicon/SumArray-e1.java");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void summation(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/carp/summation.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testHistogram(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/carp/histogram.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

}
