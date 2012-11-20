// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

public class RecordType extends Type {

  private String name[];
  private Type type[];
  public RecordType(String name[],Type type[]){
    this.name=Arrays.copyOf(name,name.length);
    this.type=Arrays.copyOf(type,type.length);
  }

  public int getFieldCount(){ return name.length; }
  
  public String getFieldName(int i){ return name[i]; }

  public Type getFieldType(int i){return type[i]; }
  
  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }
  @Override
  public boolean supertypeof(ProgramUnit context, Type t) {
    // TODO Auto-generated method stub
    return false;
  }
}

