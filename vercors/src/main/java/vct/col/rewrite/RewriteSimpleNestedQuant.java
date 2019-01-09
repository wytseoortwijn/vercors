package vct.col.rewrite;

import java.util.Arrays;

import org.apache.commons.lang3.ArrayUtils;

import vct.col.ast.ASTNode;
import vct.col.ast.Binder;
import vct.col.ast.BindingExpression;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.PrimitiveSort;
import vct.col.ast.PrimitiveType;
import vct.col.ast.ProgramUnit;

/**
 * Rewrite simple nested universal quantifiers to quantifiers with multiple
 * variables. E.g.
 * <code>\forall* decl1; guard1; (\forall* decl2; guard2; body);</code> becomes
 * <code>\forall* decl1, decl2; guard1 && guard2; body</code>.
 * 
 * @author Henk Mulder
 *
 */
public class RewriteSimpleNestedQuant extends AbstractRewriter {
  
  public RewriteSimpleNestedQuant(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(BindingExpression be) {
    if ((be.binder == Binder.Star || be.binder == Binder.Forall) && be.main instanceof BindingExpression) {
      BindingExpression be2 = (BindingExpression) be.main;
      if (be2.binder == be.binder && be2.result_type.equals(be.result_type)) {
        be2 = rewrite(be2);
        DeclarationStatement[] decls = ArrayUtils.addAll(rewrite(be.getDeclarations()), be2.getDeclarations());
        ASTNode[][] triggers = ArrayUtils.addAll(rewrite(be.triggers), be2.triggers);
        PrimitiveSort ps = (be.result_type instanceof PrimitiveType && ((PrimitiveType)be.result_type).sort == PrimitiveSort.Resource) || (be2.result_type instanceof PrimitiveType && ((PrimitiveType)be2.result_type).sort == PrimitiveSort.Resource) ? PrimitiveSort.Resource : PrimitiveSort.Boolean;
        Binder binder = ps == PrimitiveSort.Resource ? Binder.Star : Binder.Forall;
        result = create.binder(binder, create.primitive_type(ps), decls, triggers, and(rewrite(be.select), be2.select),
            be2.main);
        return;
      }
    }
    super.visit(be);
  }
  
}
