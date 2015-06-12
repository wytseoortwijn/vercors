package vct.main;

import hre.util.TestReport.Verdict;

import org.junit.Test;
import org.junit.runner.RunWith;

import com.google.code.tempusfugit.concurrency.ConcurrentTestRunner;

import static vct.main.Feature.*;

/**
 * Class that contains tests that may be broken in the current version of the
 * tool, but should be fixed in future versions.
 *  
 * @author Stefan Blom
 *
 */
@RunWith(ConcurrentTestRunner.class) 
public class BrokenTests extends ToolTest {

  @Test
  public void testSumArray(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/silicon/SumArray.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  
  @Test
  public void testSumArrayErr1(){
    sem_get();
    try {
      VCTResult res=run("vct","--silver=silicon_qp","//examples/silicon/SumArray-e1.java");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_scp_example() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "--single-group",
          "//examples/kernels/scp-example.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_scp_example_err() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "--single-group",
          "//examples/kernels/scp-example-e1.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

}
