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
public class DafnyTest extends ToolTest {
  
  public DafnyTest(){
    require(Dafny);
  }

  @Test
  public void testDafnyIncr(){
    sem_get(Dafny);
    try {
      VCTResult res=run("vct","--dafny","//examples/dafny/DafnyIncr.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testDafnyIncrE1(){
    sem_get(Dafny);
    try {
      VCTResult res=run("vct","--dafny","//examples/dafny/DafnyIncrE1.java");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }
 
}
