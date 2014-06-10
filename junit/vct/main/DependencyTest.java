package vct.main;

import java.nio.file.Paths;

import org.junit.Test;

public class DependencyTest extends ToolTest {
  
  @Test
  public void testZ3sat(){
      VCTResult res=run("z3","-smt2","//examples/backends/test-sat.smt");  
      res.mustSay("sat");
  }
  
  @Test
  public void testZ3unsat(){
      VCTResult res=run("z3","-smt2","//examples/backends/test-unsat.smt");  
      res.mustSay("sat");
  }
  
  @Test
  public void testBoogiePass(){
      VCTResult res=run("boogie","//examples/backends/test-pass.bpl");  
      res.mustSay("Boogie program verifier finished with 1 verified, 0 errors");
  }

  @Test
  public void testBoogieFail(){
      VCTResult res=run("boogie","//examples/backends/test-fail.bpl");  
      res.mustSay("Boogie program verifier finished with 0 verified, 1 error");
  }

  @Test
  public void testChalicePass(){
      VCTResult res=run("chalice","//examples/backends/test-pass.chalice");  
      res.mustSay("Boogie program verifier finished with 3 verified, 0 errors");
  }

  @Test
  public void testChaliceFail(){
      VCTResult res=run("chalice","//examples/backends/test-fail.chalice");  
      res.mustSay("Boogie program verifier finished with 2 verified, 1 error");
  }

}
