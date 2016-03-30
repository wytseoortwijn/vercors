package vct.col.rewrite;

import vct.col.ast.*;

public class AbstractMethodResolver extends AbstractRewriter {

  public AbstractMethodResolver(ProgramUnit source) {
    super(source);
  }

  @Override
  public void visit(Method m){
    ASTNode body=m.getBody();
    if(body==null){
      body=create.block(create.expression(StandardOperator.Assume,create.constant(false)));
    } else {
      body=rewrite(body);
    }
    result=create.method_kind(
        m.kind,
        rewrite(m.getReturnType()),
        rewrite(m.getContract()),
        m.name,
        rewrite(m.getArgs()),
        m.usesVarArgs(),
        body
    );
  }
}
