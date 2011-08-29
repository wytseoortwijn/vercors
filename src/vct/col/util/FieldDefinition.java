package vct.col.util;

import vct.col.ast.ASTClass;

public class FieldDefinition extends AnyDefinition{

  private ClassDefinition parent;
  
  public FieldDefinition(String name,ClassDefinition parent){
    super(name);
    this.parent=parent;
  }

  public ClassDefinition getParent() {
    return parent;
  }
  
}
