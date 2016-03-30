package vct.main;

import hre.util.TestReport.Verdict;

import org.junit.Test;
import org.junit.runner.RunWith;

import com.google.code.tempusfugit.concurrency.ConcurrentTestRunner;

import static vct.main.Feature.*;

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
      VCTResult res=run("vct","--silver=silicon_qp","//examples/carp/histogram-matrix.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testHistogramFull(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/carp/histogram-submatrix.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testAccessSubmatrix(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/carp/access-sub-matrix.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testAccessSubmatrixErr1(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/carp/access-sub-matrix-err1.c");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testZeroSubmatrix(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/carp/zero-sub-matrix.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testHistoryLoop(){
    sem_get(Histories);
    try {
      VCTResult res=run("vct","--silver=silicon","--check-history",
          "//examples/histories/History.pvl","//examples/histories/HistoryLoop.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testHistoryThreadsProcessesPVL(){
      VCTResult res=run("vct","--silver=silicon","--check-defined","//examples/threads/HistorySubject.java");
      res.checkVerdict(Verdict.Pass);
  }
  
  @Test
  public void testHistoryThreadsLemmasPVL(){
      VCTResult res=run("vct","--silver=silicon","--check-axioms","//examples/threads/HistorySubject.java");
      res.checkVerdict(Verdict.Pass);
  }
  
  @Test
  public void testHistoryThreadsApplication(){
      VCTResult res=run("vct","--silver=silicon","--check-history",
          "//examples/threads/HistorySubject.java",
          "//examples/threads/HistoryLock.java",
          "//examples/threads/SpecifiedThread.java",
          "//examples/threads/HistoryWorker.java",
          "//examples/threads/HistoryMain.java");
      res.checkVerdict(Verdict.Pass);
  }
  

  
  @Test
  public void testTranspose(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/arrays/Transpose.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testWandDemo(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//examples/encoding/WandDemoSilver.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testTreeWand(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","--silicon-z3-timeout=120000","//examples/encoding/TreeWandSilver.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testTreeWandE1(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//examples/encoding/TreeWandSilver-e1.java");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testTreeWandE2(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//examples/encoding/TreeWandSilver-e2.java");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testTreeRecursive(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//examples/encoding/TreeRecursiveSilver.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testPVLLocks(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//examples/waitnotify/Main.pvl",
          "//examples/waitnotify/Worker.pvl",
          "//examples/waitnotify/Queue.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
    
  @Test
  public void testPVLSyntax(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//pvl_examples/syntax.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }  
  }
  
  @Test
  public void testLFQbasics(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//examples/layers/LFQ.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }  
  }
  
  @Test
  public void testLFQhist(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","--check-history","//examples/layers/LFQHist.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }  
  }
  
  @Test
  public void testJava6Lock(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//examples/layers/Java6Lock.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testHistoryLFQ(){
      VCTResult res=run("vct","--silver=silicon","--check-history",
          "//examples/layers/HistoryApplication.java");
      res.checkVerdict(Verdict.Pass);
  }
  

  
}
