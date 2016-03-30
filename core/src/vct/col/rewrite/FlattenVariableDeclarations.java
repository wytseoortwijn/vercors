package vct.col.rewrite;

import java.util.HashMap;
import java.util.Map;

import vct.col.ast.ASTFlags;
import vct.col.ast.ASTNode;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.NameExpression;
import vct.col.ast.ProgramUnit;
import vct.col.ast.Type;
import vct.col.ast.VariableDeclaration;

public class FlattenVariableDeclarations extends AbstractRewriter {

  public FlattenVariableDeclarations(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(VariableDeclaration decl) {
    for(DeclarationStatement tmp:decl.flatten()){
      if (decl.isValidFlag(ASTFlags.STATIC)){
        tmp.setStatic(decl.isStatic());
      }
      current_sequence().add(tmp);
    }
    result=null;
  }

}
