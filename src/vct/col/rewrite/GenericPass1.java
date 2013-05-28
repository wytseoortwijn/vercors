package vct.col.rewrite;

import java.util.HashMap;
import java.util.Map;

import vct.col.ast.*;
import vct.col.ast.PrimitiveType.Sort;

public class GenericPass1 extends AbstractRewriter {

  public GenericPass1(ProgramUnit source) {
    super(source);
  }

  @Override
  public void visit(ASTClass cl){
    Contract c=cl.getContract();
    if (c==null){
      super.visit(cl);
      return;
    }
    Map<String,Type> map=new HashMap<String,Type>();
    MultiSubstitution sigma=new MultiSubstitution(null,map);
    for(DeclarationStatement decl:c.given){
      if (decl.getType().isPrimitive(Sort.Class)){
        map.put(decl.getName(),(Type)decl.getInit());
      }
    }
    super.visit(cl);
    result=sigma.rewrite(result);
  }
  
  @Override
  public void visit(ClassType t){
    result=create.class_type(t.getFullName());
  }
  
  @Override
  public void visit(MethodInvokation e){
    Type t=e.getType();
    Type rt=e.getDefinition().getReturnType();
    if(t.equals(rt) || (e.object instanceof Type)){
      super.visit(e);
    } else {
      Warning("invokation: %s != %s",t,rt);
      super.visit(e);
      ASTNode tmp=result;
      result=create.expression(StandardOperator.Cast,create.class_type(((ClassType)t).getFullName()),tmp);
    }
    //if (t instanceof ClassType && t.getArgCount()>0 && !(e.object instanceof Type)){
      //ASTNode tmp=create.expression(StandardOperator.Cast,create.class_type(((ClassType)t).getFullName()),rewrite(e.object));
      //result=create.invokation(tmp, e.dispatch, e.method, rewrite(e.getArgs()));
      
    //} else {
    //  super.visit(e);
    //}
  }
}
