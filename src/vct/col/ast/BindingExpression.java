package vct.col.ast;

import java.util.ArrayList;
import static hre.System.Abort;

public class BindingExpression extends ASTNode {

  public static enum Binder {LAMBDA,FORALL,EXISTS,SUM,PRODUCT,STAR};
  
  public final Binder binder;
  public final ASTNode select;
  public final ASTNode main;
  private ArrayList<DeclarationStatement> decls=new ArrayList<DeclarationStatement>();
  
  public BindingExpression(Binder binder,DeclarationStatement decls[],ASTNode select,ASTNode main){
    this.binder=binder;
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

  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor) {
    visitor.visit(this);
  }

}
