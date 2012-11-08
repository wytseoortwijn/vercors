package vct.main;

import vct.col.ast.ProgramUnit;

public abstract class CompilerPass {

  private String description;
  
  public String getDescripion(){
    return description;
  }
  
  public CompilerPass(String description){
    this.description=description;
  }
  
  public abstract ProgramUnit apply(ProgramUnit arg);

}
