package vct.main;

import java.util.Deque;

import hre.util.TestReport;
import vct.col.ast.ProgramUnit;

public abstract class CompilerPass {

  public TestReport report=new TestReport();
  
  private String description;
  
  public String getDescripion(){
    return description;
  }
  
  public CompilerPass(String description){
    this.description=description;
  }
  
  public ProgramUnit apply(ProgramUnit arg, String ... args){
    throw new hre.HREError("Class %s failed to override both apply method.",getClass());
  }

  public ProgramUnit apply(Deque<String> remainder,ProgramUnit arg, String ... args){
    return apply(arg,args);
  }
  
  public void fail(String format,Object ... args){
    report.fail(format,(Object[])args);
  }
  
  
}
