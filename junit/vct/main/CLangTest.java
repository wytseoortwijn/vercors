package vct.main;

import hre.util.TestReport.Verdict;
import org.junit.Test;
import org.junit.runner.RunWith;
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
	      
	      res.checkVerdict(Verdict.Error);
	      
	      res.mustSay("not a . <= . && . < . pattern");
	    } finally {
	      sem.release();
	    }
	  }
}
