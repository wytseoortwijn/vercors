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
import static vct.main.Feature.*;

@RunWith(ConcurrentTestRunner.class)
public class MainTest extends ToolTest {

  @Test
  public void testBoogieExample() {
    sem_get();
    try {
      VCTResult res = run("vct", "--boogie",
          "//examples/sequential/BoogieExample.java");
      res.mustSay("method F: Pass");
      res.mustSay("method G: Fail");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBoogieExamplePVL() {
    sem_get();
    try {
      VCTResult res = run("vct", "--boogie",
          "//examples/sequential/boogie-example.pvl");
      res.mustSay("method F: Pass");
      res.mustSay("method G: Fail");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testNestedLoops() {
    sem_get();
    try {
      VCTResult res = run("vct", "--boogie",
          "//examples/sequential/nested-loops.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testLoopsPVL() {
    sem_get();
    try {
      VCTResult res = run("vct", "--boogie",
          "//examples/sequential/loopinv-pvl.pvl");
      res.mustSay("method f_ok: Pass");
      res.mustSay("method f_bad: Fail");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testBoogieTest() {
    sem_get();
    try {
      VCTResult res = run("vct", "--boogie",
          "//examples/sequential/BoogieTest.java");
      res.mustSay("method abs: Pass");
      res.mustSay("method bad_incr_1: Fail");
      res.mustSay("method good_incr_1: Pass");
      res.mustSay("method good_incr_2: Pass");
      res.mustSay("method good_incr_3: Pass");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }

  }

  @Test
  public void testBoogieGlobals() {
    sem_get();
    try {
      VCTResult res = run("vct", "--boogie", "--infer-modifies",
          "//examples/sequential/BoogieWithGlobals.java");
      res.mustSay("method add: Pass");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testLoopInv() {
    sem_get();
    try {
      VCTResult res = run("vct", "--boogie",
          "//examples/sequential/LoopInv.java");
      res.mustSay("method f_ok: Pass");
      res.mustSay("method f_bad: Fail");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testSimpleExamples() {
    sem_get();
    try {
      VCTResult res = run("vct", "--boogie",
          "//examples/sequential/SimpleExamples.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testIncr() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/permissions/Incr.java");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testRosterFixed() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/permissions/RosterFixed.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testSwapInteger() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/permissions/SwapInteger.java");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
      res.mustSay("The postcondition might not hold.");
    } finally {
      sem.release();
    }
  }

  @Test
  public void testSwapLong() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/permissions/SwapLong.java");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
      res.mustSay("The postcondition might not hold.");
    } finally {
      sem.release();
    }
  }

  @Test
  public void testSwapDouble() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/permissions/SwapDouble.java");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
      res.mustSay("The postcondition might not hold.");
    } finally {
      sem.release();
    }
  }

  @Test
  public void testCounter() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/permissions/Counter.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testTreeStack() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/permissions/TreeStack.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testBox() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/permissions/box.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testBadLoop1() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/permissions/BadLoop1.java");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testBadLoop2() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/permissions/BadLoop2.java");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testMultiIncrement() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/permissions/MultiIncrement.java");
      res.mustSay("The final verdict is Pass");
    } finally {
      sem.release();
    }
  }

  @Test
  public void testIntegerList() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/predicates/IntegerList.java");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testRoster() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/encoding/Roster.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testCounterState() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/encoding/CounterState.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testTwice() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/encoding/Twice.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testAtomicReadWrite() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/atomics/AtomicReadWrite.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testGetters() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit", "--witness-inline",
          "//examples/encoding/Getters.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testDWLock() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/atomics/DWLock.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testSingleCell() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/atomics/SingleCell.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testLockExample() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/locks/LockExample.java");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testReentLock() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/atomics/ReentLock.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testSimpleThread() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/inheritance/SimpleThread.java",
          "//examples/inheritance/SimpleThreadMain.java",
          "//examples/inheritance/SimpleThreadInstance.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testZeroArrayChalice() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/arrays/ZeroArray.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testZeroArraySilicon() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp",
          "//examples/arrays/ZeroArray.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testBadTypePVL() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//examples/manual/BadType.pvl");
      res.mustSay("type of left argument is Resource rather than boolean");
      res.checkVerdict(Verdict.Error);
      sem.release();
    } finally {
      sem.release();
    }
  }

  @Test
  public void testBadTypeJava() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//examples/manual/BadType.java");
      res.mustSay("first argument of Perm must be");
      res.checkVerdict(Verdict.Error);
      sem.release();
    } finally {
      sem.release();
    }
  }

  @Test
  public void testRBLock() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/atomics/RBLock.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testRBProdCons() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/atomics/RBProdCons.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testRBSingleCell() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/atomics/RBSingleCell.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testTreeRecursive() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/predicates/TreeRecursive.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testListAppend() {
    sem_get(MagicWand);
    try {
      VCTResult res = run("vct", "--silver=silicon", "--inline", "//examples/encoding/ListAppend.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testWandDemo() {
    sem_get(MagicWand);
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/encoding/WandDemo.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testWitnessDemo() {
    sem_get(MagicWand);
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/encoding/WitnessDemo.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testCountDownLatch() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/synchronizers/CountDownLatch.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testSemaphore() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/synchronizers/Semaphore.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testReentrantLock() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit",
          "//examples/synchronizers/ReentrantLock.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testCounterPVL() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//pvl_examples/Counter.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testCounterPVLerr1() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//pvl_examples/Counter-e1.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testFibonacciPVL() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//pvl_examples/fibonacci.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testFibonacciPVLerr1() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//pvl_examples/fibonacci-e1.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testUpdatePoint() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/forkjoin/update-point.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testMinMax() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/predicates/minmax-list.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testPredicatesPVL() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit", "--witness-inline",
          "//pvl_examples/predicates.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testLockSetDemoErr() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon","//examples/locks/lockset-demo.java");
      res.checkVerdict(Verdict.Fail);
      res.mustSay("unfold.failed:insufficient.permission");
    } finally {
      sem.release();
    }
  }

}
