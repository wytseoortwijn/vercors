// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;
import java.io.PrintStream;

import hre.ast.Origin;

/** common features of all AST nodes. */
public abstract class ASTNode {

  private static long next_id=0;


  /** Even though some nodes cannot be static, they can all
      occur in a block, and thus their status must be esy to get. */
  private boolean is_static=false;

  public boolean isStatic(){
    return is_static;
  }

  public void setStatic(boolean val){
    is_static=val;
  }

  private long id;

  public ASTNode() {
    synchronized(ASTNode.class/*this.getClass()*/){
      this.id=next_id;
      ++next_id;
    }
  }

  private Origin origin;
  
  public void setOrigin(ASTNode node){
    setOrigin(node.origin);
  }
  
  public void setOrigin(Origin origin){
    if (origin==null) throw new Error("illegal null origin");
    if (this.origin!=null) throw new Error("origin already set");
    this.origin=origin;
  }
  
  public Origin getOrigin(){
    return origin;
  }
  
  public abstract <T> void accept_simple(ASTVisitor<T> visitor);
  
  public final <T> void accept(ASTVisitor<T> visitor){
    if (visitor instanceof ASTFrame) {
      ((ASTFrame) visitor).enter(this);
    }
    visitor.pre_visit(this);
    this.accept_simple(visitor);
    visitor.post_visit(this);
    if (visitor instanceof ASTFrame) {
      ((ASTFrame) visitor).leave(this);
    }
  }
  
  public final <T> T apply(ASTVisitor<T> visitor){
    this.accept(visitor);
    return visitor.getResult();
  }

  public long getUniqueID(){
    return id;
  }
  
  private Type t=null;

  public Type getType() {
    return t;
  }
  public void setType(Type t){
    this.t=t;
  }
  
  private ASTNode parent;
  
  public ASTNode getParent(){
    return parent;
  }

  public void setParent(ASTNode parent){
    if (parent==null){
      throw new Error("illegal null parent");
    }
    if (this.parent!=null){
      throw new Error("modifying parent");
    }
    this.parent=parent;
  }
  
  public final void accept_if(ASTVisitor v){
    if (v!=null) accept(v);
  }
  
}
