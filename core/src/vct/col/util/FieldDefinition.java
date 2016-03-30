package vct.col.util;

import vct.col.ast.ASTClass;

public class FieldDefinition extends AnyDefinition{

  private ClassDefinition parent;
  public final boolean is_static;
  
  public FieldDefinition(String name,boolean is_static,ClassDefinition parent){
    super(name);
    this.parent=parent;
    this.is_static=is_static;
  }

  public ClassDefinition getParent() {
    return parent;
  }
  
}
