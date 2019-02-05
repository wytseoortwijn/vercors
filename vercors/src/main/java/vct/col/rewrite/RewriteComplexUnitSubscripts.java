package vct.col.rewrite;

import java.util.HashSet;

import vct.col.ast.ASTNode;
import vct.col.ast.BindingExpression;
import vct.col.ast.ConstantExpression;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveSort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.RecursiveVisitor;
import vct.col.ast.StandardOperator;
import vct.col.util.ASTUtils;

public class RewriteComplexUnitSubscripts extends AbstractRewriter {
  
  private int replCount;
  
  public RewriteComplexUnitSubscripts(ProgramUnit pu) {
    super(pu);
  }
  
  @Override
  public void visit(BindingExpression e) {
    switch (e.binder) {
    case Forall:
    case Star:
      if (e.triggers == null || e.triggers.length == 0) {
        ASTNode main = rewrite(e.main);
        ASTNode select = e.select;
        HashSet<DeclarationStatement> decls = new HashSet<DeclarationStatement>();
        for (DeclarationStatement decl : e.getDeclarations()) {
          decls.add(decl);
        }
        HashSet<ASTNode> complexSubscripts = new HashSet<ASTNode>();
        collectComplexSubscripts(complexSubscripts, and(select, main));
        boolean success = !complexSubscripts.isEmpty();
        while (!complexSubscripts.isEmpty()) {
          ASTNode subs = complexSubscripts.iterator().next();
          String varName = getVar();
          DeclarationStatement decl = create.field_decl(varName, create.primitive_type(PrimitiveSort.Integer));
          decls.add(decl);
          NameExpression var = create.local_name(varName);
          main = ASTUtils.replace(subs, var, main);
          select = ASTUtils.replace(subs, var, select);
          select = and(select, eq(var, subs));
          complexSubscripts = new HashSet<ASTNode>();
          collectComplexSubscripts(complexSubscripts, and(select, main));
        }
        if (success) {
          result = create.binder(e.binder, e.result_type, decls.toArray(new DeclarationStatement[0]), e.triggers,
              select, main);
          Debug(String.format("Changed unit subscript %s\n to %s", e, result));
        } else {
          result = create.binder(e.binder, e.result_type, e.getDeclarations(), e.triggers, e.select, rewrite(e.main));
        }
      } else {
        super.visit(e);
      }
      break;
    default:
      super.visit(e);
    }
  }
  
  private static void collectComplexSubscripts(HashSet<ASTNode> complexSubscripts, ASTNode tree) {
    RecursiveVisitor<Boolean> scanner = new RecursiveVisitor<Boolean>((ProgramUnit) null) {
      @Override
      public void visit(OperatorExpression e) {
        if (e.isa(StandardOperator.Subscript) && hasComplex(e.second())) {
          complexSubscripts.add(e.second());
        } else {
          super.visit(e);
        }
      }
    };
    tree.accept(scanner);
  }
  
  private static boolean hasComplex(ASTNode tree) {
    if (tree instanceof NameExpression || tree instanceof ConstantExpression) {
      return false;
    } else {
      return true;
    }
  }
  
  private String getVar() {
    return "unit_var_" + (++replCount);
  }
}
