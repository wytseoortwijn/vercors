package vct.main;

import static org.junit.Assert.*;
import hre.io.Message;
import hre.io.MessageProcess;
import hre.util.TestReport.Verdict;

import java.io.File;
import java.net.URL;
import java.security.Permission;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Semaphore;

import junit.framework.TestCase;

import org.junit.Test;
import org.junit.runner.RunWith;

import sun.applet.Main;
import vct.util.Configuration;

import com.google.code.tempusfugit.concurrency.ConcurrentTestRunner;

class VCTResult {
  public Verdict verdict=null;
  public final List<Message> log=new ArrayList<Message>();
  public void mustSay(String string) {
    for(Message msg:log){
      if (msg.getFormat().equals("stdout: %s")||msg.getFormat().equals("stderr: %s")){
        if (((String)msg.getArg(0)).indexOf(string)>=0) return;
      }
    }
    fail("expected output "+string+" not found");
  };
  public void checkVerdict(Verdict res){
    if (verdict != res) fail("bad result : "+verdict);
  }
}

@RunWith(ConcurrentTestRunner.class) 
public class MainTest extends TestCase {
  
  private static Semaphore sem=new Semaphore(Runtime.getRuntime().availableProcessors());
  
  public void sem_get(){
    try {
      sem.acquire();
    } catch (InterruptedException e) {
      fail("test interrupted");
      return;
    }
   
  }
  
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
  
  public VCTResult run(String ... args){
    VCTResult res=new VCTResult();
    ClassLoader loader=Configuration.class.getClassLoader();
    URL url=loader.getResource("vct/util/Configuration.class");
    File f=new File(url.getFile());
    for(int i=0;i<5;i++) f=f.getParentFile();
    System.err.printf("home is %s%n", f);
    String OS=System.getProperty("os.name");
    String vct;
    if (OS.startsWith("Windows")){
      vct=f+"/windows/bin/";
    } else {
      vct=f+"/unix/bin/";
    }
    args[0]=vct+args[0];
    for(int i=1;i<args.length;i++){
      if (args[i].startsWith("//")){
        args[i]=f+args[i].substring(1);
      }
    }
    MessageProcess p=new MessageProcess(args);
    for(;;){
      Message msg=p.recv();
      res.log.add(msg);
      if (msg==null){
        fail("unexpected null message");
      }
      System.err.printf(msg.getFormat(), msg.getArgs());
      System.err.println();
      if (msg.getFormat().equals("exit %d")){
        int n=(Integer)msg.getArg(0);
        if (n>0){
          fail("bad exit status "+n);
        }
        break;
      }
      if (((String)msg.getArg(0)).contains("The final verdict is Pass")){
        if (res.verdict!=null) fail("repeated verdict");
        res.verdict=Verdict.Pass;
      }
      if (((String)msg.getArg(0)).contains("The final verdict is Fail")){
        if (res.verdict!=null) fail("repeated verdict");
        res.verdict=Verdict.Fail;
      }
    }
    if (res.verdict==null) fail("missing verdict");
    return res;
  }

}
