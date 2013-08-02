package vct.col.ast;

import java.util.Arrays;

import vct.util.ClassName;

public class ASTSpecial extends ASTNode {

  public static enum Kind {
    Comment
  };

  public final Kind kind;
  
  public final ASTNode[] args;
  
  public ASTSpecial(Kind kind,ASTNode ... args){
    this.kind=kind;
    this.args=Arrays.copyOf(args,args.length);
  }

  @Override
  protected <T> void accept_simple(ASTVisitor<T> visitor) {
    visitor.visit(this);
  }

}
