// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

import vct.col.ast.Method.Kind;

/**
 * Method Declaration.
 * @author sccblom
 *
 */
public class Method extends ASTNode {
  public static enum Kind{Constructor,Predicate,Pure,Plain};

  private final String name;
  private final FunctionType t;
  private final String args[];
  private Contract contract;
  private ASTNode body;
  private static int mods;
  public final Kind kind;
  
  public Method(String name,Type return_type,Contract contract,ASTNode args[],ASTNode body){
    this(Kind.Plain,name,return_type,contract,args,body);
  }
  /*
  public Method(Kind kind, ASTClass cl,String name,String args[],FunctionType t){
    this.cl=cl;
    this.name=name;
    this.t=t;
    this.args=Arrays.copyOf(args,args.length);
    cl.addMethod(name,this);
    this.kind=kind;
  }
*/
  public Method(Kind kind, String name,String args[],FunctionType t){
    this.name=name;
    this.t=t;
    this.args=Arrays.copyOf(args,args.length);
    this.kind=kind;
  }
  
  public Method(Kind kind, String name,Type return_type,Contract contract,ASTNode args[],ASTNode body){
    this.name=name;
    int N=args.length;
    Type args_type[]=new Type[N];
    this.args=new String[N];
    for(int i=0;i<N;i++){
      DeclarationStatement par=(DeclarationStatement)args[i];
      this.args[i]=par.getName();
      args_type[i]=par.getType();
    }
    this.contract=contract;
    this.t=new FunctionType(args_type,return_type);
    this.body=body;
    this.kind=kind;
  }

  public Kind getKind(){ return kind; }
    
  public String getName(){ return name; }

  public int getArity(){ return args.length; }

  public String getArgument(int i){ return args[i]; }

  public FunctionType getType(){ return t; }

  public void setContract(Contract contract){
    this.contract=contract;
  }
  public Contract getContract(){
    return contract;
  }
  public void setModifiers(int mods){
    this.mods=mods;
  }
  public int getModifiers(){
    return this.mods;
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
    int N=args.length;
    DeclarationStatement decls[]=new DeclarationStatement[N];
    for(int i=0;i<N;i++){
      decls[i]=new DeclarationStatement(args[i],t.getArgument(i));
      decls[i].setOrigin(getOrigin());
    }
    return decls;
  }

}


