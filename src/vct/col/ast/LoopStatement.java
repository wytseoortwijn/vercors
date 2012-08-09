// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.ArrayList;
import java.util.Collection;

public class LoopStatement extends ASTNode {
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
}

