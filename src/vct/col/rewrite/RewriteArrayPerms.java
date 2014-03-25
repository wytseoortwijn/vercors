package vct.col.rewrite;

import vct.col.ast.*;
import vct.java.printer.JavaPrinter;

public class RewriteArrayPerms extends AbstractRewriter {

  public RewriteArrayPerms(ProgramUnit source) {
    super(source);
  }

  @Override
  public void visit(BindingExpression e){
    if (e.binder==BindingExpression.Binder.STAR){
      if (e.getDeclCount()!=1) Fail("no rules for more than one declaration");
      DeclarationStatement decl=e.getDeclaration(0);
      if (!e.select.isa(StandardOperator.And)) {
        Fail("select is not a conjunction");
      }
      ASTNode left=((OperatorExpression)e.select).getArg(0);
      ASTNode right=((OperatorExpression)e.select).getArg(1);
      if (!left.isa(StandardOperator.LTE)
        ||!right.isa(StandardOperator.LT)
      ){
        Fail("not a . <= . && . < . pattern");
      }
      ASTNode lower=((OperatorExpression)left).getArg(0);
      ASTNode var1=((OperatorExpression)left).getArg(1);
      ASTNode var2=((OperatorExpression)right).getArg(0);
      ASTNode upper=((OperatorExpression)right).getArg(1);
      if (!(var1 instanceof NameExpression)
      ||  !(((NameExpression)var1).getName().equals(decl.getName()))
      ||  !(var2 instanceof NameExpression)
      ||  !(((NameExpression)var2).getName().equals(decl.getName()))
      ){
        Fail("not a . <= i && i < . pattern");
      }
      if (e.main.isa(StandardOperator.Perm)){
        ASTNode loc=((OperatorExpression)e.main).getArg(0);
        ASTNode frac=((OperatorExpression)e.main).getArg(1);
        if (!loc.isa(StandardOperator.Subscript)){
          Fail("non-array Perm inside quantification");
        }
        ASTNode array_name=((OperatorExpression)loc).getArg(0);
        ASTNode index_expr=((OperatorExpression)loc).getArg(1);
        if (index_expr.isName(decl.getName())){
          result=create.expression(StandardOperator.ArrayPerm,
              rewrite(array_name),
              rewrite(lower),
              create.constant(1),
              rewrite(upper),
              rewrite(frac)
          );
        } else if (index_expr.isa(StandardOperator.Mod)){
          OperatorExpression idx=(OperatorExpression)index_expr;
          if (!sameAST(upper,idx.getArg(1))){
            System.out.printf("upper: ");
            vct.util.Configuration.getDiagSyntax().print(System.out,upper);
            System.out.printf("%nidx: ");
            vct.util.Configuration.getDiagSyntax().print(System.out,idx.getArg(1));
            System.out.printf("%n");
            Fail("modulo support is limited to modulo upper limit");
          }
          if (!idx.getArg(0).isa(StandardOperator.Plus) && !idx.getArg(0).isa(StandardOperator.Minus)){
            Warning("unrecognized array index expression");
            vct.util.Configuration.getDiagSyntax().print(System.err,idx.getArg(0));
            System.err.println();
            Fail("exit");
          }
          OperatorExpression idx2=(OperatorExpression)idx.getArg(0);
          if (idx2.getArg(0).isName(decl.getName())/* && (idx2.getArg(1) instanceof ConstantExpression)*/){
            result=create.expression(StandardOperator.ArrayPerm,
                rewrite(array_name),
                rewrite(lower),
                create.constant(1),
                rewrite(upper),
                rewrite(frac)
            );            
          } else {
            Fail("unrecognized array index expression");
          }
        } else if (index_expr.isa(StandardOperator.Plus)) {
          OperatorExpression idx=(OperatorExpression)index_expr;
          if (!idx.getArg(0).isa(StandardOperator.Mult)){
            Warning("array index expression not of form c * x + e");
            vct.util.Configuration.getDiagSyntax().print(System.err,idx);
            System.err.println();
            Fail("exit");
          }
          OperatorExpression idx2=(OperatorExpression)idx.getArg(0);
          if (idx2.getArg(1).isName(decl.getName())/* && (idx2.getArg(0) instanceof ConstantExpression)*/){
            result=create.expression(StandardOperator.ArrayPerm,
                rewrite(array_name),
                create.expression(StandardOperator.Plus,
                    create.expression(StandardOperator.Mult,
                        rewrite(idx2.getArg(0)),
                        rewrite(lower)),
                    rewrite(idx.getArg(1))),
                rewrite(idx2.getArg(0)),
                create.expression(StandardOperator.Minus,
                    rewrite(upper),rewrite(lower)),
                rewrite(frac)
            );            
          } else {
            Warning("array index expression not of form c * x + e");
            vct.util.Configuration.getDiagSyntax().print(System.err,idx);
            System.err.println();
            Fail("exit");
          }
        } else {
          Warning("unrecognized array index expression");
          vct.util.Configuration.getDiagSyntax().print(System.err,index_expr);
          System.err.println();
          Fail("exit");          
        }
      } else {
        Warning("unrecognized main");
        vct.util.Configuration.getDiagSyntax().print(System.err,e.main);
        System.err.println();
        Fail("exit");
      }
    } else {
      super.visit(e);
    }
  }

  @Override public void visit(OperatorExpression e){
    if (e.getOperator()==StandardOperator.Perm){
      ASTNode loc=((OperatorExpression)e).getArg(0);
      ASTNode frac=((OperatorExpression)e).getArg(1);
      if (loc.isa(StandardOperator.Subscript)){
        ASTNode array_name=((OperatorExpression)loc).getArg(0);
        ASTNode index_expr=((OperatorExpression)loc).getArg(1);
        if (!index_expr.isReserved(ASTReserved.Any)){
          result=create.expression(StandardOperator.ArrayPerm,
              rewrite(array_name),
              rewrite(index_expr),
              create.constant(1),
              create.constant(1),
              rewrite(frac)
          );
          return;
        }
      }
    }
    super.visit(e);
  }
  private boolean sameAST(ASTNode ast1, ASTNode ast2) {
    if (ast1 instanceof NameExpression){
      return ast2.isName(((NameExpression)ast1).getName());
    }
    return false;
  }
  

  
}
