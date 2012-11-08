package vct.col.rewrite;

import vct.col.ast.ASTNode;
import vct.col.ast.Contract;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.ProgramUnit;

import static vct.col.ast.StandardOperator.Perm;
import static vct.col.ast.StandardOperator.Star;

public class ForallRule extends AbstractRewriter {

  public ForallRule(ProgramUnit source) {
    super(source);
  }

  public void visit(Method m){
    boolean predicate=m.getKind()==Method.Kind.Predicate;
    if (predicate){
      String name=m.getName();
      ASTNode body=rewrite(m.getBody());
      for(DeclarationStatement d:m.getArgs()){
        currentClass.add_dynamic(rewrite(d));
        ASTNode perm=create.expression(Perm,create.field_name(d.getName()),create.constant(50));
        body=create.expression(Star,perm,body);
      }
      result=create.predicate(name, body);
    } else {
      Contract c=m.getContract();
      for(DeclarationStatement d:c.given){
        currentClass.add_dynamic(rewrite(d));
      }
      m.setContract(new Contract(new DeclarationStatement[0],new DeclarationStatement[0],c.modifies,c.pre_condition,c.post_condition));
      super.visit(m);
    }
  }
  
  public void visit(MethodInvokation e){
    if (e.getDefinition().getKind()==Method.Kind.Predicate){
      // TODO: check / generate requirements
      result=create.invokation(rewrite(e.object), e.guarded, e.method);
    } else {
      super.visit(e);
    }
  }
}
