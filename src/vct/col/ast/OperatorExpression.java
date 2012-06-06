// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.ast.FileOrigin;

import java.util.*;

import static hre.System.*;

public class OperatorExpression extends ASTNode {

  private StandardOperator op;
  private ASTNode args[];

  public OperatorExpression(StandardOperator op,ASTNode ... args){
    this.op=op;
    this.args=Arrays.copyOf(args,args.length);
    if (args.length != op.arity()) Abort("wrong number of arguments for %s, got %d expected %d",op,args.length,op.arity());
  }
  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }
  
  public StandardOperator getOperator(){
    return op;
  }
  
  public ASTNode getArg(int i){
    if (i>=args.length){
      throw new Error("operator "+op+" does not have an argument "+i);
    }
    return args[i];
  }

  public void mergeOrigins(){
    if (args.length < 2) throw new Error("cannot merge on less than 2 arguments");
    FileOrigin start,end;
    if (args[0].getOrigin() instanceof FileOrigin) {
      start=(FileOrigin)args[0].getOrigin();
    } else {
      throw new Error("merge requires FileOrigin");
    }
    if (args[args.length-1].getOrigin() instanceof FileOrigin) {
      end=(FileOrigin)args[args.length-1].getOrigin();
    } else {
      throw new Error("merge requires FileOrigin");
    }
    setOrigin(start.merge(end));
  }
  
  public static OperatorExpression create(StandardOperator op,ASTNode ... args){
    OperatorExpression res=new OperatorExpression(op,args);
    res.mergeOrigins();
    return res;
  }
  public ASTNode[] getArguments() {
    return Arrays.copyOf(args,args.length);
  }
}

