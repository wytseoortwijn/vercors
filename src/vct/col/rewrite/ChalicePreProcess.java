package vct.col.rewrite;

import vct.col.ast.Dereference;
import vct.col.ast.MethodInvokation;
import vct.col.ast.PrimitiveType;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;

public class ChalicePreProcess extends AbstractRewriter {

  public ChalicePreProcess(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(MethodInvokation e){
    if (e.method.equals("length") && e.object.getType().isPrimitive(PrimitiveType.Sort.Sequence)){
      result=create.expression(StandardOperator.Size,rewrite(e.object));
    } else {
      super.visit(e);
    }
  }
  
  @Override
  public void visit(Dereference e){
    if (e.field.equals("length") && e.object.getType().isPrimitive(PrimitiveType.Sort.Sequence)){
      result=create.expression(StandardOperator.Size,rewrite(e.object));
    } else {
      super.visit(e);
    }    
  }
    
     
}
