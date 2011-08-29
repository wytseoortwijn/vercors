package vct.col.util;

import vct.col.ast.Type;

public class LocalDefinition extends AnyDefinition{

  private Type type; 
  public LocalDefinition(String name,Type type){
    super(name);
    this.type=type;
  }

  public Type getType() {
    return type;
  }
  
}
