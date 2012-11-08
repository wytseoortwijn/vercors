// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.ast.CompositeOrigin;
import hre.ast.MessageOrigin;
import hre.ast.Origin;

import java.util.*;


import static vct.col.ast.StandardOperator.And;

public class ContractBuilder {

  private boolean empty=true;
  
  private final static Origin origin=new MessageOrigin("contract builder default true");
  public final static ASTNode default_true=new ConstantExpression(true,origin);
  private ASTNode pre_condition=default_true;
  private ASTNode post_condition=default_true;
  private ArrayList<DeclarationStatement> given=new ArrayList<DeclarationStatement>();
  private ArrayList<DeclarationStatement> yields=new ArrayList<DeclarationStatement>();
  private HashSet<ASTNode> modifiable;
  
  private static final void scan_to(ArrayList<DeclarationStatement> list,BlockStatement decls){
    int N=decls.getLength();
    for(int i=0;i<N;i++){
      ASTNode d=decls.getStatement(i);
      if (d instanceof DeclarationStatement){
        DeclarationStatement decl=(DeclarationStatement)d;
        if (decl.getInit()!=null) throw new Error("illegal initialization");
        list.add(decl);
      } else {
        throw new Error("not a declaration: "+d.getClass());
      }
    }
  }
  
  /**
   * Add the given declarations to the list of given variables.
   * @param decls A block consisting of declaration statement only.
   */
  public void given(BlockStatement decls){
    empty=false;
    scan_to(given,decls);
  }
  /**
   * Add the given declarations to the list of yielded variables.
   * @param decls
   */
  public void yields(BlockStatement decls){
    empty=false;
    scan_to(yields,decls);    
  }
  /**
   * Add the given declarations to the list of given variables.
   * @param decls Any number of declarations.
   */
  public void given(DeclarationStatement ... decls){
    empty=false;
    for(DeclarationStatement d:decls) given.add(d);
  }
  /**
   * Add the given declarations to the list of yielded variables.
   * @param decls Any number of declarations.
   */
  public void yields(DeclarationStatement ... decls){
    empty=false;
    for(DeclarationStatement d:decls) yields.add(d);
  }
  public void ensures(ASTNode condition){
    empty=false;
    if (condition.getOrigin()==null) throw new Error("condition "+condition.getClass()+" without origin");
    if (post_condition==default_true) {
      post_condition=condition;
    } else {
      ASTNode tmp=post_condition;
      post_condition=new OperatorExpression(StandardOperator.And,post_condition,condition);
      post_condition.setOrigin(new CompositeOrigin(tmp.getOrigin(),condition.getOrigin()));
    }
  }
  public void requires(ASTNode condition){
    empty=false;
    if (condition.getOrigin()==null) throw new Error("condition "+condition.getClass()+" without origin");
    if (pre_condition==default_true) {
      pre_condition=condition;
    } else {
      ASTNode tmp=post_condition;
      pre_condition=new OperatorExpression(StandardOperator.And,pre_condition,condition);
      pre_condition.setOrigin(new CompositeOrigin(tmp.getOrigin(),condition.getOrigin()));
    }
  }
 
  public Contract getContract(){
    if (empty) return null;
    DeclarationStatement[] decls=new DeclarationStatement[0];
    ASTNode[] mods=null;
    if (modifiable!=null){
      mods=modifiable.toArray(new ASTNode[0]);
    }
    return new Contract(given.toArray(decls),yields.toArray(decls),mods,pre_condition,post_condition);
  }
  public void modifies(ASTNode ... locs) {
    empty=false;
    if (modifiable==null) modifiable=new HashSet<ASTNode>();
    for (ASTNode loc : locs){
      modifiable.add(loc);
    }
  }

  public static Contract emptyContract() {
    return new Contract(new DeclarationStatement[0],new DeclarationStatement[0],default_true,default_true);
  }

}

