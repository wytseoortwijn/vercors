package vct.main;

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
  
  public abstract ProgramUnit apply(ProgramUnit arg, String ... args);

  public void fail(String format,Object ... args){
    report.fail(format,(Object[])args);
  }
  
  
}
