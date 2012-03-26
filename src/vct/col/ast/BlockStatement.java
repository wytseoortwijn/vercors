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

  /*
  public void add_or_merge(ASTNode body) {
    if (body instanceof BlockStatement){
      for(ASTNode node:((BlockStatement)body).block){
        node.resetParent();
        add_statement(body);
      }
    } else {
      add_statement(body);
    }
  }
  */
}

