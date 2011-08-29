// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;


public class BlockStatement extends ASTNode {

  private ArrayList<ASTNode> block=new ArrayList();
  
  public void add_statement(ASTNode s){
    block.add(s);
    s.setParent(this);
  }

  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }
 
  public int getLength(){ return block.size(); }
  
  public ASTNode getStatement(int i){ return block.get(i); }
  
  public boolean isEmpty(){
    return block.isEmpty();
  }

}

