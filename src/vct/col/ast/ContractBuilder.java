// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.ast.CompositeOrigin;
import hre.ast.MessageOrigin;
import hre.ast.Origin;

import java.util.*;


import static vct.col.ast.StandardOperator.And;

public class ContractBuilder {

  private final static Origin origin=new MessageOrigin("contract builder default true");
  public final static ASTNode default_true=new ConstantExpression(true,origin);
  private ASTNode pre_condition=default_true;
  private ASTNode post_condition=default_true;
  private static int modifiers=0;
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
  public void given(BlockStatement decls){
    scan_to(given,decls);
  }
  public void yields(BlockStatement decls){
    scan_to(yields,decls);    
  }
  public void ensures(ASTNode condition){
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
    if (condition.getOrigin()==null) throw new Error("condition "+condition.getClass()+" without origin");
    if (pre_condition==default_true) {
      pre_condition=condition;
    } else {
      ASTNode tmp=post_condition;
      pre_condition=new OperatorExpression(StandardOperator.And,pre_condition,condition);
      pre_condition.setOrigin(new CompositeOrigin(tmp.getOrigin(),condition.getOrigin()));
    }
  }
  
  public void addModifiers(int mod){
    modifiers|=mod;
  }

  public Contract getContract(){
    DeclarationStatement[] decls=new DeclarationStatement[0];
    ASTNode[] mods=null;
    if (modifiable!=null){
      mods=modifiable.toArray(new ASTNode[0]);
    }
    return new Contract(mods,pre_condition,post_condition,
        given.toArray(decls),
        yields.toArray(decls),modifiers);
  }
  public void modifies(ASTNode ... locs) {
    if (modifiable==null) modifiable=new HashSet<ASTNode>();
    for (ASTNode loc : locs){
      modifiable.add(loc);
    }
  }

}

