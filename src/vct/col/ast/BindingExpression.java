package vct.col.ast;

import java.util.ArrayList;
import static hre.System.Abort;

public class BindingExpression extends ASTNode {

  public static enum Binder {LAMBDA,FORALL,EXISTS,SUM,PRODUCT,STAR};
  
  public final Binder binder;
  public final ASTNode select;
  public final ASTNode main;
  private ArrayList<DeclarationStatement> decls=new ArrayList<DeclarationStatement>();
  
  public BindingExpression(Binder binder,BlockStatement decls,ASTNode select,ASTNode main){
    this.binder=binder;
    this.select=select;
    this.main=main;
    int N=decls.getLength();
    for(int i=0;i<N;i++){
      ASTNode n=decls.getStatement(i);
      if (n instanceof DeclarationStatement){
        this.decls.add((DeclarationStatement)n);
      } else {
        Abort("found %s among declarations for binding expression",n.getClass());
      }
    }
  }
  
  public int getDeclCount(){
    return decls.size();
  }
  
  public DeclarationStatement getDeclaration(int i){
    return decls.get(i);
  }

  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor) {
    visitor.visit(this);
  }

}
