// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.ast.MessageOrigin;

import java.util.ArrayList;
import java.util.Collection;

public class LoopStatement extends ASTNode implements BeforeAfterAnnotations {
  private ArrayList<ASTNode> invariants=new ArrayList();
  private ASTNode body;
  private ASTNode entry_guard;
  private ASTNode exit_guard;
  private ASTNode init_block;
  private ASTNode update_block;
  
  public void setInitBlock(ASTNode init_block){
    this.init_block=init_block;
  }
  public ASTNode getInitBlock(){
    return init_block;
  }

  public void setUpdateBlock(ASTNode update_block){
    this.update_block=update_block;
  }
  public ASTNode getUpdateBlock(){
    return update_block;
  }

  public void setBody(ASTNode body){
    this.body=body;
  }
  public ASTNode getBody() {
    return this.body;
  }

  public void setEntryGuard(ASTNode entry_guard){
    this.entry_guard=entry_guard;
  }
  public ASTNode getEntryGuard(){
    return entry_guard;
  }
  
  public void setExitGuard(ASTNode exit_guard){
    this.exit_guard=exit_guard;
  }
  public ASTNode getExitGuard(){
    return exit_guard;
  }

  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }

  public void prependInvariant(ASTNode inv){
    invariants.add(0,inv);
  }
  
  public void appendInvariant(ASTNode inv){
    invariants.add(inv);
  }
  
  public Collection<ASTNode> getInvariants(){
    return invariants;
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
  public void set_before(BlockStatement block){
    before=block;
  }
  public BlockStatement get_before(){
    if (before==null) {
      before=new BlockStatement();
      before.setOrigin(new MessageOrigin("before block"));
    }
    return before;
  }
  public void set_after(BlockStatement block){
    after=block;
  }
  public BlockStatement get_after(){
    if (after==null) {
      after=new BlockStatement();
      after.setOrigin(new MessageOrigin("after block"));
    }
    return after;
  }

}

