package vct.col.rewrite;

import vct.col.ast.ASTNode;
import vct.col.ast.ClassType;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.util.ClassName;

public class SimplifyCalls extends AbstractRewriter {

  public void visit(MethodInvokation e) {
    ASTNode object=rewrite_nullable(e.object);
    if (object instanceof NameExpression){
      NameExpression name=(NameExpression)object;
      if (name.getKind()==NameExpression.Kind.Reserved && name.getName().equals("this")){
        object=null;
      }
    } else if (object instanceof ClassType) {
      ClassType t=(ClassType)object;
      if (ClassName.equal(t.getNameFull(),current_class().getFullName())){
        object=null;
      }
    }
    NameExpression method=rewrite_and_cast(e.method);
    int N=e.getArity();
    ASTNode args[]=new ASTNode[N];
    for(int i=0;i<N;i++){
      args[i]=e.getArg(i).apply(this);
    }
    result=create.invokation(object,e.guarded,method,args);
  }

}
