package vct.col.rewrite;

import java.util.HashMap;

import vct.col.ast.ASTNode;
import vct.col.ast.ASTReserved;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.ProgramUnit;

public class InlinePredicatesRewriter extends AbstractRewriter {

  public InlinePredicatesRewriter(ProgramUnit source) {
    super(source);
  }

  
  @Override
  public void visit(MethodInvokation e){
    Method def=e.getDefinition();
    if (def==null){
      Abort("invokation of undefined method.");
    }
    int N=def.getArity();
    if (def.kind!=Method.Kind.Predicate || def.isRecursive()){
      super.visit(e);
    } else {
      HashMap<NameExpression,ASTNode> map=new HashMap<NameExpression, ASTNode>();
      Substitution sigma=new Substitution(source(),map);
      map.put(create.reserved_name(ASTReserved.This), rewrite(e.object));
      for(int i=0;i<N;i++){
        map.put(create.unresolved_name(def.getArgument(i)),rewrite(e.getArg(i)));
      }
      result=sigma.rewrite(def.getBody());
    }
  }

  @Override
  public void visit(Method m){
    if (m.kind==Method.Kind.Predicate && !m.isRecursive()){
      result=null;
    } else {
      super.visit(m);
    }
  }
}
