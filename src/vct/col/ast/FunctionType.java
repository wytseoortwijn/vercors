// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

public class FunctionType extends Type {

  private Type args[];
  private Type result;
  public FunctionType(Type args[],Type result){
    this.args=Arrays.copyOf(args,args.length);
    this.result=result;
  }

  public int getArity(){ return args.length; }
  
  public Type getResult(){ return result; }
  
  public Type getArgument(int i){ return args[i]; }
  
  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }
  @Override
  public boolean supertypeof(Type t) {
    // TODO Auto-generated method stub
    return false;
  }

}
