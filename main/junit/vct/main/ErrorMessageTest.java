package vct.main;

import hre.util.TestReport.Verdict;
import org.junit.Test;
import org.junit.runner.RunWith;
import com.google.code.tempusfugit.concurrency.ConcurrentTestRunner;

@RunWith(ConcurrentTestRunner.class) 
public class ErrorMessageTest extends ToolTest {
  
  @Test
  public void test_tree_solution() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice","//examples/errors/type_error.pvl");
      res.checkVerdict(Verdict.Error);
      res.mustSay("Types of left and right-hand side argument are uncomparable");
    } finally {
      sem.release();
    }
  }

}
