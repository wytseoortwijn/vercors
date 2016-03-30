package vct.main;

import vct.col.ast.ProgramUnit;
import hre.util.TestReport;

public abstract class ValidationPass {
  
  private String description;
  
  public String getDescripion(){
    return description;
  }
  
  public ValidationPass(String description){
    this.description=description;
  }
  
  public abstract TestReport apply(ProgramUnit arg,String ... args);

}
