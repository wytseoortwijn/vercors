package vct.col.ast;

import java.util.Arrays;

import vct.util.ClassName;

public class ASTSpecial extends ASTNode {

  public static enum Kind {
    Assert,
    Comment,
    Expression,
    Invariant,
//    Fold
    With,
    Then,
    Proof,
    Import,
    Throw,
    Label,
    Contract, Requires, Ensures, Given, Yields, Modifies
  };

  public final Kind kind;
  
  public final ASTNode[] args;
  
  public ASTSpecial(Kind kind,ASTNode ... args){
    this.kind=kind;
    this.args=Arrays.copyOf(args,args.length);
  }

  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }
  public <T> T accept_simple(ASTMapping<T> map){
    return map.map(this);
  }
  
  public boolean isSpecial(Kind with) {
    return kind==with;
  }

}
