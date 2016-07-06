package vct.col.rewrite;

import vct.col.ast.*;

public class ConvertTypeExpressions extends AbstractRewriter {

  public ConvertTypeExpressions(ProgramUnit source) {
    super(source);
  }
  
  
  @Override
  public void visit(Method m){
    Method res=copy_rw.rewrite(m);
    Type t=m.getReturnType();
    while(t instanceof TypeExpression){
      TypeExpression e=(TypeExpression)t;
      switch(e.op){
      case Static:
        res.setStatic(true);
        t=e.types[0];
        break;
      case Extern:
        res.setFlag(ASTFlags.EXTERN,true);
        t=e.types[0];
        break;        
      default:
        Fail("cannot deal with type operator %s",e.op);
      }
    }
    System.err.printf("remaining type of %s is %s%n",m.getReturnType(),t);
    result=create.method_decl(t,res.getContract(),res.name,res.getArgs(),res.getBody());
    result.copyMissingFlags(res);
  }

}
