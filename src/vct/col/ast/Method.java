// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.ast.MessageOrigin;

import java.util.*;

import vct.col.ast.Method.Kind;

/**
 * Method Declaration.
 * @author sccblom
 *
 */
public class Method extends ASTNode {
  /** Enumeration of kinds of methods. */
  public static enum Kind{
    Constructor,
    Predicate,
    Pure,
    Plain
  };

  private final String name;
  private final Type return_type;
  private final DeclarationStatement args [];
  private Contract contract;
  private ASTNode body;
  public final Kind kind;
  
  public Method(String name,Type return_type,Contract contract,DeclarationStatement args[],ASTNode body){
    this(Kind.Plain,name,return_type,contract,args,body);
  }

  public Method(Kind kind, String name,String args[],FunctionType t){
    this.name=name;
    this.return_type=t.getResult();
    this.args=new DeclarationStatement[args.length];
    for(int i=0;i<args.length;i++){
      this.args[i]=new DeclarationStatement(args[i],t.getArgument(i));
      this.args[i].setParent(this);
      this.args[i].setOrigin(new MessageOrigin("dummy origin for argument "+i));
    }
    this.kind=kind;
  }
  
  public Method(Kind kind, String name,Type return_type,Contract contract,DeclarationStatement args[],ASTNode body){
    this.name=name;
    this.return_type=return_type;
    this.args=Arrays.copyOf(args,args.length);
    for(int i=0;i<args.length;i++){
      if (this.args[i].getParent()==null) this.args[i].setParent(this);
    }
    this.contract=contract;
    this.body=body;
    this.kind=kind;
  }

  public Kind getKind(){ return kind; }
    
  public String getName(){ return name; }

  public int getArity(){ return args.length; }

  public String getArgument(int i){ return args[i].getName(); }

  public Type getArgType(int i){ return args[i].getType(); }

  public void setContract(Contract contract){
    this.contract=contract;
  }
  public Contract getContract(){
    return contract;
  }
  
  public void setBody(ASTNode body){
    this.body=body;
  }
  public ASTNode getBody(){
    return body;
  }
  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }
  public DeclarationStatement[] getArgs() {
    return args;
  }
  public Type getReturnType() {
    return return_type;
  }

}


