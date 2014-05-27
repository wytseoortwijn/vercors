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
    } finally {
      sem.release();
    }
    
  }
  
  /*

testBoogieGlobals(){
  runVCT "--boogie --infer-modifies --no-context" BoogieWithGlobals
  mustSay "method add: Pass"
  mustSay "The final verdict is Pass"
}

testLoopInv(){
  runVCT "--boogie --no-context" LoopInv
  mustSay "method f_ok: Pass"
  mustSay "method f_bad: Fail"
  mustSay "The final verdict is Fail"
}

testSimpleExamples(){
  runVCT "--boogie --no-context" SimpleExamples
  mustSay "The final verdict is Pass"
}

testIncr(){
  runVCT "--chalice --no-context" Incr
  mustSay "The final verdict is Fail"
}

testRosterFixed(){
  runVCT "--chalice --no-context" RosterFixed
  mustSay "The final verdict is Pass"
}

testSwapInteger(){
  runVCT "--chalice --no-context" SwapInteger
  mustSay "The final verdict is Fail"
  mustSay "error at file .* line 34 .* The postcondition might not hold."
}

testSwapLong(){
  runVCT "--chalice --no-context" SwapLong
  mustSay "The final verdict is Fail"
  mustSay "error at file .* line 34 .* The postcondition might not hold."
}

testSwapDouble(){
  runVCT "--chalice --no-context" SwapDouble
  mustSay "The final verdict is Fail"
  mustSay "error at file .* line 34 .* The postcondition might not hold."
}

testCounter(){
  runVCT "--chalice --no-context" Counter
  mustSay "The final verdict is Pass"
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
  
/*

testIntegerList(){
  runVCT "--chalice --no-context" IntegerList
  mustSay "The final verdict is Fail"
}

testTreeWand(){
  runVCT "--chalice --inline --no-context" TreeWand
  mustSay "The final verdict is Pass"
}

testRoster(){
  runVCT "--chalice --explicit --no-context" Roster
  mustSay "The final verdict is Pass"
}

testCounterState(){
  runVCT "--chalice --explicit --no-context" CounterState
  mustSay "The final verdict is Pass"
}

testTwice(){
  runVCT "--chalice --explicit --no-context" Twice
  mustSay "The final verdict is Pass"
}

testAtomicReadWrite(){
  runVCT "--chalice --explicit --no-context" AtomicReadWrite
  mustSay "The final verdict is Pass"
}

testGetters(){
  runVCT "--chalice --explicit --no-context --witness-inline" Getters
  mustSay "The final verdict is Pass"
}

testDWLock(){
  runVCT "--chalice --explicit --no-context" DWLock
  mustSay "The final verdict is Pass"
}

testSingleCell(){
  runVCT "--chalice --explicit --no-context" SingleCell
  mustSay "The final verdict is Pass"
}

testLockExample(){
  runVCT "--chalice --explicit --no-context" LockExample
  mustSay "The final verdict is Fail"
}

testReentLock(){
  runVCT "--chalice --explicit --no-context" ReentLock
  mustSay "The final verdict is Pass"
}

testSimpleThread(){
  runVCT "--chalice --no-context" SimpleThread SimpleThreadMain SimpleThreadInstance
  mustSay "The final verdict is Pass"
}

# too slow in current version
#testFullThread(){
#  runVCT "--chalice --explicit --no-context" FullThreadInstance FullThread FullThreadMain
#  mustSay "The final verdict is Pass"
#}

# too slow in current version
#testFibonacci (){
#  runVCT "--chalice --explicit --no-context" Fibonacci FullThread
#  mustSay "The final verdict is Pass"
#}

testZeroArray (){
  runVCT "--chalice --no-context" ZeroArray
  mustSay "The final verdict is Pass"
}

testRBLock (){
  runVCT "--chalice --explicit --no-context" RBLock
  mustSay "The final verdict is Pass"
}

testRBProdCons (){
  runVCT "--chalice --explicit --no-context" RBProdCons
  mustSay "The final verdict is Pass"
}

testRBSingleCell (){
  runVCT "--chalice --explicit --no-context" RBSingleCell
  mustSay "The final verdict is Pass"
}

testTreeRecursive (){
  runVCT "--chalice --no-context" TreeRecursive
  mustSay "The final verdict is Pass"
}

testListAppend (){
  runVCT "--chalice --inline --no-context" ListAppend
  mustSay "The final verdict is Pass"
}

# too slow in current version
#testListIterator (){
#  runVCT "--chalice --inline --no-context" ListIterator
#  mustSay "The final verdict is Pass"
#}

testWandDemo (){
  runVCT "--chalice --no-context" WandDemo
  mustSay "The final verdict is Pass"
}

testWitnessDemo (){
  runVCT "--chalice --explicit --no-context" WitnessDemo
  mustSay "The final verdict is Pass"
}

testCountDownLatch (){
  runVCT "--chalice --explicit --no-context" CountDownLatch
  mustSay "The final verdict is Pass"
}

# commented out because it triggers a bug in the Chalice/Boogie/Z3 stack.
#testSemaphore (){
#  runVCT "--chalice --explicit --no-context" Semaphore
#  mustSay "The final verdict is Pass"
#}

testReentrantLock (){
  runVCT "--chalice --explicit --no-context" ReentrantLock
  mustSay "The final verdict is Pass"
}

 */

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
