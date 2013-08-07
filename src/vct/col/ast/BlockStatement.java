// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;


public class BlockStatement extends ASTNode implements ASTSequence<BlockStatement> {

  private ArrayList<ASTNode> block=new ArrayList();
  
  public void add_statement(ASTNode s){
    block.add(s);
    s.setParent(this);
  }
  
  public int getLength(){ return block.size(); }
  
  public ASTNode getStatement(int i){ return block.get(i); }
  
  public boolean isEmpty(){
    return block.isEmpty();
  }

  @Override
  public Iterator iterator() {
    return block.iterator();
  }

  @Override
  public BlockStatement add(ASTNode item) {
    block.add(item);
    return this;
  }

  @Override
  public int size() {
    return block.size();
  }

  @Override
  public ASTNode get(int i) {
    return block.get(i);
  }

  @Override
  protected <T> void accept_simple(ASTVisitor<T> visitor) {
    visitor.visit(this);
  }

}

