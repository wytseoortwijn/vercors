package vct.col.rewrite;

import java.util.HashMap;
import java.util.Map;

import vct.col.ast.ASTNode;
import vct.col.ast.BindingExpression;
import vct.col.ast.ClassType;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.util.ASTUtils;
import vct.util.ClassName;

public class SimplifyExpressions extends AbstractRewriter {

  public SimplifyExpressions(ProgramUnit source) {
    super(source);
  }

  public void visit(BindingExpression e) {
    switch(e.binder){
      case FORALL:
      case STAR:
      {
        if (e.getDeclCount()==1){
          DeclarationStatement decl=e.getDeclaration(0);
          String name=decl.getName();
          ASTNode main=e.main;
          if (main.isa(StandardOperator.Implies)){
            OperatorExpression implication=(OperatorExpression)main;
            if (implication.getArg(0).isa(StandardOperator.EQ) &&
                !ASTUtils.find_name(implication.getArg(1), name)
            ){
              OperatorExpression eq=(OperatorExpression)implication.getArg(0);
              if (eq.getArg(0).isName(name)&&!ASTUtils.find_name(implication.getArg(1), name)){
                ASTNode val=rewrite(eq.getArg(1));
                Map<NameExpression, ASTNode> map=new HashMap();
                map.put(create.identifier(name), val);
                Substitution sigma=new Substitution(source(),map);
                result=create.expression(StandardOperator.Implies,sigma.rewrite(e.select),rewrite(implication.getArg(1)));
                return;
              }
            } else {
              result=create.binder(e.binder, rewrite(e.getType()),rewrite(e.getDeclarations()),
                  create.expression(StandardOperator.And,
                      rewrite(e.select),
                      rewrite(implication.getArg(0))
                      ),
                  rewrite(implication.getArg(1)));
              return;
            }
          }
        }
        super.visit(e);
        return;
      }
      default:
        super.visit(e);
    }
  }

}
