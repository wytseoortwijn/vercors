package vct.main;

import hre.util.TestReport.Verdict;
import org.junit.Test;
import org.junit.runner.RunWith;
import com.google.code.tempusfugit.concurrency.ConcurrentTestRunner;

@RunWith(ConcurrentTestRunner.class) 
public class SiliconInternalTest extends ToolTest {
  
  @Test
  public void testBasicArithmetic(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/arithmetic.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicAssert(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/assert.sil");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicElsif(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/elsif.sil");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicFold(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/fold.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicFunc2(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/func2.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicFunc3(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/func3.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicFuncPred(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/funcpred.sil");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicFunc(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/func.sil");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicHeap(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/heap.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicMethods(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/methods.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testBasicNames(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/names.sil");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicNew(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/new.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicOld(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/old.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicQuantifiers(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/quantifiers.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  //@Test
  public void testBasicSimpleDomain(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/simple_domain.sil");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicUnfolding(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/unfolding.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicWellDef(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/welldef.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBasicWhile(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon","//silver/examples/basic/while.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testQuantSeqArray(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//silver/examples/quantifiedpermissions/sequences/array.sil");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testQuantSeqTestopt(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//silver/examples/quantifiedpermissions/sequences/testopt.sil");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  // disabled because it started taking too much time... @Test
  public void testQuantSeqBsearch(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//silver/examples/quantifiedpermissions/sequences/bsearch.sil");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testQuantSeqMergesort(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//silver/examples/quantifiedpermissions/sequences/mergesort.sil");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testBasicAssertOK(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//examples/silver/BasicAssert.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testBasicAssertE1(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon",
          "//examples/silver/BasicAssert-e1.java");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

}
