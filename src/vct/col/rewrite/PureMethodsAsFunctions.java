package vct.col.rewrite;

import hre.HREError;
import vct.col.ast.*;

/**
 * Transform function definitions written in statement syntax (pure methods)
 * into expression syntax.
 *  
 * @author Stefan Blom
 *
 */
public class PureMethodsAsFunctions extends AbstractRewriter {

  public PureMethodsAsFunctions(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(Method m){
    if (m.kind==Method.Kind.Pure && (m.getBody() instanceof BlockStatement)){
      Type returns=rewrite(m.getReturnType());
      Contract contract=rewrite(m.getContract());
      DeclarationStatement args[]=rewrite(m.getArgs());
      ASTNode body=do_body((BlockStatement)m.getBody(),0);
      result=create.function_decl(returns, contract, m.name, args, body);
    } else {
      super.visit(m);
    }
  }

  private ASTNode do_body(BlockStatement body, int i) {
    ASTNode S=body.get(i);
    ASTNode res;
    create.enter();
    create.setOrigin(S.getOrigin());
    if (S instanceof ReturnStatement){
      ReturnStatement R=(ReturnStatement)S;
      res=rewrite(R.getExpression());
    } else if (S.isa(StandardOperator.Unfold)) {
      OperatorExpression e=(OperatorExpression)S;
      res=create.expression(StandardOperator.Unfolding,rewrite(e.getArg(0)),do_body(body,i+1));
    } else {
      throw new HREError("unsupported pure statement %s",S);
    }
    create.leave();
    return res;
  }

}
