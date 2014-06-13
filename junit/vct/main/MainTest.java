package vct.main;

import static org.junit.Assert.*;
import hre.io.Message;
import hre.io.MessageProcess;
import hre.util.TestReport.Verdict;

import java.io.File;
import java.net.URL;
import java.security.Permission;
import java.util.concurrent.Semaphore;

import junit.framework.TestCase;

import org.junit.Test;
import org.junit.runner.RunWith;

import sun.applet.Main;
import vct.util.Configuration;

import com.google.code.tempusfugit.concurrency.ConcurrentTestRunner;

@RunWith(ConcurrentTestRunner.class) 
public class MainTest extends ToolTest {
  
  @Test
  public void testBoogieExample(){
    sem_get();
    try {
      VCTResult res=run("vct","--boogie","//examples/sequential/BoogieExample.java");
      res.mustSay("method F: Pass");
      res.mustSay("method G: Fail");
      if (res.verdict != Verdict.Fail) fail("bad result : "+res.verdict);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testBoogieTest(){
    sem_get();
    try {
      VCTResult res=run("vct","--boogie","//examples/sequential/BoogieTest.java");
      res.mustSay("method abs: Pass");
      res.mustSay("method bad_incr_1: Fail");
      res.mustSay("method good_incr_1: Pass");
      res.mustSay("method good_incr_2: Pass");
      res.mustSay("method good_incr_3: Pass");
      if (res.verdict != Verdict.Fail) fail("bad result : "+res.verdict);
    } finally {
      sem.release();
    }
    
  }
  
  /*

testBoogieGlobals(){
  sem_get();
    try {
      VCTResult res=run( "vct","--boogie --infer-modifies --no-context" BoogieWithGlobals
  mustSay "method add: Pass"
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}

testLoopInv(){
  sem_get();
    try {
      VCTResult res=run( "vct","--boogie --no-context" LoopInv
  mustSay "method f_ok: Pass"
  mustSay "method f_bad: Fail"
  if (res.verdict != Verdict.Fail) fail("bad result : "+res.verdict);
}

testSimpleExamples(){
  sem_get();
    try {
      VCTResult res=run( "vct","--boogie --no-context" SimpleExamples
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}

testIncr(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice --no-context" Incr
  if (res.verdict != Verdict.Fail) fail("bad result : "+res.verdict);
}

testRosterFixed(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice --no-context" RosterFixed
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}

testSwapInteger(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice --no-context" SwapInteger
  if (res.verdict != Verdict.Fail) fail("bad result : "+res.verdict);
  mustSay "error at file .* line 34 .* The postcondition might not hold."
}

testSwapLong(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice --no-context" SwapLong
  if (res.verdict != Verdict.Fail) fail("bad result : "+res.verdict);
  mustSay "error at file .* line 34 .* The postcondition might not hold."
}

testSwapDouble(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice --no-context" SwapDouble
  if (res.verdict != Verdict.Fail) fail("bad result : "+res.verdict);
  mustSay "error at file .* line 34 .* The postcondition might not hold."
}

testCounter(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice --no-context" Counter
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}

   */
  @Test
  public void testBadLoop1(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","//examples/permissions/BadLoop1.java");
      if (res.verdict != Verdict.Fail) fail("bad result : "+res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testBadLoop2(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","//examples/permissions/BadLoop2.java");
      if (res.verdict != Verdict.Fail) fail("bad result : "+res.verdict);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testMultiIncrement(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","//examples/permissions/MultiIncrement.java");
      res.mustSay("The final verdict is Pass");
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void 
testIntegerList(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice", "//examples/predicates/IntegerList.java");
  if (res.verdict != Verdict.Fail) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testTreeWand(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--inline","//examples/encoding/TreeWand.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testRoster(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit","//examples/encoding/Roster.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testCounterState(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit" ,"//examples/encoding/CounterState.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testTwice(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit" ,"//examples/encoding/Twice.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testAtomicReadWrite(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit" ,"//examples/atomics/AtomicReadWrite.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testGetters(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit","--witness-inline" ,"//examples/encoding/Getters.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testDWLock(){
  sem_get();
    try {
      VCTResult res=run("vct", "--chalice","--explicit" ,"//examples/atomics/DWLock.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testSingleCell(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit" ,"//examples/atomics/SingleCell.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testLockExample(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit" ,"//examples/locks/LockExample.java");
  if (res.verdict != Verdict.Fail) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testReentLock(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit" ,"//examples/atomics/ReentLock.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testSimpleThread(){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice",
          "//examples/inheritance/SimpleThread.java",
          "//examples/inheritance/SimpleThreadMain.java",
          "//examples/inheritance/SimpleThreadInstance.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}

/*
# too slow in current version
#testFullThread(){
#  sem_get();
    try {
      VCTResult res=run( "vct","--chalice --explicit --no-context" FullThreadInstance FullThread FullThreadMain
#  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
#}

# too slow in current version
#testFibonacci (){
#  sem_get();
    try {
      VCTResult res=run( "vct","--chalice --explicit --no-context" Fibonacci FullThread
#  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
#}
*/
  @Test
  public void 
testZeroArray (){
  sem_get();
    try {
      VCTResult res=run("vct","--chalice", "//examples/arrays/ZeroArray.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testRBLock (){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit" ,"//examples/atomics/RBLock.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testRBProdCons (){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit" ,"//examples/atomics/RBProdCons.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testRBSingleCell (){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit" ,"//examples/atomics/RBSingleCell.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testTreeRecursive (){
  sem_get();
    try {
      VCTResult res=run("vct",  "--chalice","//examples/predicates/TreeRecursive.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testListAppend (){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--inline","//examples/encoding/ListAppend.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}

/*
# too slow in current version
#testListIterator (){
#  sem_get();
    try {
      VCTResult res=run( "vct","--chalice --inline --no-context" ListIterator
#  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
#}
*/
  @Test
  public void 
testWandDemo (){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","//examples/encoding/WandDemo.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testWitnessDemo (){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit","//examples/encoding/WitnessDemo.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}finally {
  sem.release();
}
}
  @Test
  public void 
testCountDownLatch (){
  sem_get();
    try {
      VCTResult res=run( "vct", "--chalice","--explicit","//examples/synchronizers/CountDownLatch.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}
    finally {
      sem.release();
    }
  }
/*
# commented out because it triggers a bug in the Chalice/Boogie/Z3 stack.
#testSemaphore (){
#  sem_get();
    try {
      VCTResult res=run( "vct","--chalice --explicit --no-context" Semaphore
#  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
#}
*/
  
  @Test
  public void 
testReentrantLock (){
  sem_get();
    try {
      VCTResult res=run( "vct","--chalice","--explicit","//examples/synchronizers/ReentrantLock.java");
  if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
}
    finally {
      sem.release();
    }
  }


  /* template:
  @Test
  public void test(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","//examples/sequential/BoogieTest.java");
      checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
*/
  
  @Test
  public void testCounterPVL(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","//pvl_examples/Counter.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testCounterPVLerr1(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","//pvl_examples/Counter-e1.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testFibonacciPVL(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","//pvl_examples/fibonacci.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testFibonacciPVLerr1(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","//pvl_examples/fibonacci-e1.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testAdditionPVL(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","--single-group","//pvl_examples/addition.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testAdditionPVLerr1(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","--single-group","//pvl_examples/addition-e1.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

}
