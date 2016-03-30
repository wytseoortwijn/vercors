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

import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;

import sun.applet.Main;
import vct.util.Configuration;

import com.google.code.tempusfugit.concurrency.ConcurrentTestRunner;
import static vct.main.Feature.*;

@RunWith(ConcurrentTestRunner.class) 
public class SlowTest extends ToolTest {
  
  @Test
  public void testListIterator(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","//examples/encoding/ListIterator.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testFibonacciFull(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","--explicit",
          "//examples/inheritance/Fibonacci.java",
          "//examples/inheritance/FullThread.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  // broken test
  public void testFullThread(){
    sem_get();
    try {
      VCTResult res=run("vct","--chalice","--explicit",
          "//examples/inheritance/FullThreadInstance.java",
          "//examples/inheritance/FullThread.java",
          "//examples/inheritance/FullThreadMain.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testTreeWand() {
    sem_get(MagicWand);
    try {
      VCTResult res = run("vct", "--chalice", "--inline",
          "//examples/encoding/TreeWand.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testTreeWandErr() {
    sem_get(MagicWand);
    try {
      VCTResult res = run("vct", "--chalice", "--inline",
          "//examples/encoding/TreeWand-err.java");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

}
