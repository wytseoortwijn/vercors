package vct.col.rewrite;

import vct.col.ast.ASTNode;
import vct.col.ast.ASTReserved;
import vct.col.ast.ConstantExpression;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import static hre.System.Abort;

public class RewriteDoubleDefinition extends AbstractRewriter {

  public RewriteDoubleDefinition(ProgramUnit source) {
    super(source);
  }
  public void visit(PrimitiveType t){
    if (t.sort==Sort.Double){
      result=create.class_type(DefineDouble.double_name);
    } else {
      super.visit(t);
    }
  }
  public void visit(OperatorExpression e){
    String name;
    if (e.getType()==null) Abort("missing type for code from %s",e.getOrigin());
    if (!e.getType().isDouble()){
      super.visit(e);
      return;     
    }
    switch(e.getOperator()){
    case Plus:
      name=("plus");
      break;
    case Mult:
      name=("mult");
      break;
    default:
      super.visit(e);
      return;
    }
    int N=e.getOperator().arity();
    ASTNode args[]=new ASTNode[N];
    for(int i=0;i<N;i++) args[i]=e.getArg(i).apply(this);
    result=create.invokation(null, null, name ,args);
  }
  public void visit(ConstantExpression e){
    if(e.getType().isDouble()){
      result=create.reserved_name(ASTReserved.Null);
    } else {
      super.visit(e);
    }
  }
}
