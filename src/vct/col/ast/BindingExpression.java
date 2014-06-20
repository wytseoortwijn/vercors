package vct.col.ast;

import java.util.ArrayList;

import static hre.System.Abort;

public class BindingExpression extends ASTNode {

  public static enum Binder {LAMBDA,FORALL,EXISTS,SUM,PRODUCT,STAR,LET};
  
  public final Binder binder;
  public final ASTNode select;
  public final ASTNode main;
  public final Type result_type;
  
  private ArrayList<DeclarationStatement> decls=new ArrayList<DeclarationStatement>();
  
  public BindingExpression(Binder binder,Type result_type,DeclarationStatement decls[],ASTNode select,ASTNode main){
    this.binder=binder;
    this.result_type=result_type;
    this.select=select;
    this.main=main;
    for (DeclarationStatement decl:decls){
      this.decls.add(decl);
    }
  }
  
  public int getDeclCount(){
    return decls.size();
  }
  
  public DeclarationStatement getDeclaration(int i){
    return decls.get(i);
  }

  public DeclarationStatement[] getDeclarations(){
    return decls.toArray(new DeclarationStatement[0]);
  }
  
  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }
  public <T> T accept_simple(ASTMapping<T> map){
    return map.map(this);
  }

}
