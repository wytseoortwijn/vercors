package vct.col.rewrite;

import vct.col.ast.NameExpression;
import vct.col.ast.ProgramUnit;

public class ResolvNames extends AbstractRewriter {

  public ResolvNames(ProgramUnit source) {
    super(source);
  }

  @Override()
  public void visit(NameExpression e){
    switch(e.getKind()){
      case Unresolved:{
        VariableInfo info=variables.lookup(e.getName());
        if (info!=null){
          result=create.name(info.kind,e.getName());
          break;
        }
        Warning("unresolved name: %s, assuming field",e.getName());
        result=create.name(NameExpression.Kind.Field,e.getName());
        break;
      }
      default:
        result=create.name(e.getKind(),e.getName());
        break;
    }
  }
  
}
