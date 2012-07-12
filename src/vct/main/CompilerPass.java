package vct.main;

import vct.col.ast.ASTClass;

public abstract class CompilerPass {

  private String description;
  
  public String getDescripion(){
    return description;
  }
  
  public CompilerPass(String description){
    this.description=description;
  }
  
  public abstract ASTClass apply(ASTClass arg);

}
