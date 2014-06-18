// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.HREError;
import hre.ast.MessageOrigin;

import java.util.ArrayList;
import java.util.Collection;

import vct.col.util.ASTUtils;

public class LoopStatement extends ASTNode implements BeforeAfterAnnotations {

  private ContractBuilder cb=new ContractBuilder(); 
  private Contract contract;
  private ASTNode body;
  private ASTNode entry_guard;
  private ASTNode exit_guard;
  private ASTNode init_block;
  private ASTNode update_block;

  public void fixate(){
    if (contract!=null && cb==null) return;
    if (cb==null){
      throw new HREError("loop contract has already been fixated");
    }
    contract=cb.getContract(false);
  }
  
  public void setContract(Contract contract){
    if (cb==null){
      throw new HREError("loop contract has already been fixated");
    }
    cb=null;
    this.contract=contract;
  }
  
  public Contract getContract(){
    if (contract==null){
      throw new HREError("contract has not been fixated");
    }
    return contract;
  }

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
    cb.prependInvariant(inv);
  }
  
  public void appendInvariant(ASTNode inv){
    cb.appendInvariant(inv);
  }
  
  public Iterable<ASTNode> getInvariants(){
    return ASTUtils.conjuncts(contract.invariant,StandardOperator.Star);
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
  public LoopStatement set_before(BlockStatement block){
    before=block;
    return this;
  }
  public BlockStatement get_before(){
    if (before==null) {
      before=new BlockStatement();
      before.setOrigin(new MessageOrigin("before block"));
    }
    return before;
  }
  public LoopStatement set_after(BlockStatement block){
    after=block;
    return this;
  }
  public BlockStatement get_after(){
    if (after==null) {
      after=new BlockStatement();
      after.setOrigin(new MessageOrigin("after block"));
    }
    return after;
  }

  public void appendContract(Contract contract) {
    cb.appendInvariant(contract.invariant);
    cb.requires(contract.pre_condition);
    cb.ensures(contract.post_condition);
  }

}

