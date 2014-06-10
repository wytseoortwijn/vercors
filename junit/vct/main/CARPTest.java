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
public class CARPTest extends ToolTest {
  
  @Test
  public void testZeroArrayC(){
    sem_get();
    try {       
      VCTResult res=run("vct","--chalice","//examples/carp/zero-array-ic.c");  
      if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
    } finally {
      sem.release();
    }
  }
  @Test
  public void testZeroArrayJava(){
    sem_get();
    try {       
      VCTResult res=run("vct","--chalice","//examples/carp/ZeroArrayIC.java");  
      if (res.verdict != Verdict.Pass) fail("bad result : "+res.verdict);
    } finally {
      sem.release();
    }
  }

}
