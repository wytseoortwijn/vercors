package vct.antlr4.parser;


import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTSpecial;
import vct.col.ast.BeforeAfterAnnotations;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.rewrite.AbstractRewriter;

/**
 * Rewrite a PVL AST, produced by parsing, to conform to the COL AST standard.  
 */
public class PVLPostProcessor extends AbstractRewriter {

  public PVLPostProcessor(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(ASTClass c){
    super.visit(c);
    if (c.kind==ClassKind.Kernel) return;
    ASTClass decl=(ASTClass)result;
    int N=0;
    for(Method m:decl.dynamicMethods()){
      if (m.kind==Method.Kind.Constructor) N++;
    }
    if (N==0) create.addZeroConstructor(decl);
  }

}
