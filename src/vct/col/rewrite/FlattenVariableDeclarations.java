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
    Map<String,Type> map=new HashMap();
    AbstractRewriter rw=new MultiSubstitution(source(),map);
    map.put("basetype",decl.basetype);
    for(DeclarationStatement d:decl.get()){
      Debug("duplicating declaration for %s",d.getName());
      DeclarationStatement tmp=create.field_decl(d.getName(),rw.rewrite(d.getType()), rewrite(d.getInit()));
      if (decl.isValidFlag(ASTFlags.STATIC)){
        tmp.setStatic(decl.isStatic());
      }
      current_sequence().add(tmp);
    }
    result=null;
  }

}
