package vct.col.rewrite;

import vct.col.ast.*;

public class ConvertTypeExpressions extends AbstractRewriter {

  public ConvertTypeExpressions(ProgramUnit source) {
    super(source);
  }
  
  private KernelBodyRewriter kbr=new KernelBodyRewriter(source());
  
  @Override
  public void visit(DeclarationStatement d){
    boolean extern=false;
    Type t=d.getType(); 
    while(t instanceof TypeExpression){
      TypeExpression e=(TypeExpression)t;
      switch(e.op){
      case Static:
        t=e.types[0];
        break;
      case Extern:
        extern=true;
        t=e.types[0];
        break;        
      default:
        Fail("cannot deal with type operator %s",e.op);
      }
    }
    DeclarationStatement res=create.field_decl(d.name,rewrite(t),rewrite(d.getInit()));
    if (extern){
      res.setFlag(ASTFlags.EXTERN,true);
    }
    result=res;
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
    Method out=create.method_decl(t,res.getContract(),res.name,res.getArgs(),res.getBody());
    out.copyMissingFlags(res);
    if(kernel){
      result=kbr.rewrite(out);
    } else {
      result=out;
    }
  }

}
