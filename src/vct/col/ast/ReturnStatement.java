// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.ast.MessageOrigin;

import java.util.*;

public class ReturnStatement extends ASTNode implements BeforeAfterAnnotations {

  private ASTNode expression;
  
  public ReturnStatement(){
    expression=null;
  }

  public ReturnStatement(ASTNode e){
    expression=e;
  }
  
  public ASTNode getExpression() { return expression; }

  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }
  @Override
  public <T> T accept_simple(ASTMapping<T> map){
    return map.map(this);
  }

  /** Block of proof hints to be executed just before
   *  evaluating the expression represented by this AST node.
   *  But after any argument has been evaluated.
   */
  private BlockStatement before;
  /** Block of proof hints to be executed after the
   *  current node has been evaluated.
   */
  private BlockStatement after;
  
  public ReturnStatement set_before(BlockStatement block){
    before=block;
    if (block!=null) {
      block.setParent(this);
      if (block.getOrigin()==null){
        block.setOrigin(new MessageOrigin("before block"));
      }
    }
    return this;
  }
  public BlockStatement get_before(){
    if (before==null) set_before(new BlockStatement());
    return before;
  }
  
  public ReturnStatement set_after(BlockStatement block){
    after=block;
    if (block!=null) {
      block.setParent(this);
      if (block.getOrigin()==null){
        block.setOrigin(new MessageOrigin("after block"));
      }
    }
    return this;
  }
  public BlockStatement get_after(){
    if (after==null) set_after(new BlockStatement());
    return after;
  }

}

