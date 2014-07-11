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
public class CLangTest extends ToolTest {
  
	 @Test
	  public void testSimpleC(){
	    sem_get();
	    try {	    	
	      VCTResult res=run("vct","--chalice","//examples/clang/SimpleC.c");  
	      
	      if (res.verdict != Verdict.Pass)
	          fail("bad result : " + res.verdict);
	      
	    } finally {
	      sem.release();
	    }
	  }

	 @Test
	  public void testLoopInv(){
	    sem_get();
	    try {	    	
	      VCTResult res=run("vct","--chalice","//examples/clang/LoopInvariant.c");  
	      
	      if (res.verdict != Verdict.Pass)
	          fail("bad result : " + res.verdict);
	    } finally {
	      sem.release();
	    }
	  }
	@Test
  public void testIterationContract(){
    sem_get();
    try {    	
      VCTResult res=run("vct","--chalice","//examples/clang/ZeroArrayIC.c");  
      
      if (res.verdict != Verdict.Pass)
          fail("bad result : " + res.verdict);
    } finally {
    	
      sem.release();
    }
  }
	@Test
	public void testIndepParLoop(){
	    sem_get();
	    try {
	      VCTResult res=run("vct","--chalice","//examples/clang/Indep_ParLoop.c");    
	      
	      if (res.verdict != Verdict.Pass)
	          fail("bad result : " + res.verdict);
	    } finally {
	      sem.release();
	    }
	  }
	@Test
	public void testDepParLoop(){
	    sem_get();
	    try {
	      VCTResult res=run("vct","--chalice","//examples/clang/Dep_ParLoop.c");   
	      
	      if (res.verdict != Verdict.Pass)
	          fail("bad result : " + res.verdict);
	    } finally {
	      sem.release();
	    }
	  }
}
