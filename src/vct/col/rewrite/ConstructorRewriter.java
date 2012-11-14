package vct.col.rewrite;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import static hre.System.*;

public class ConstructorRewriter extends AbstractRewriter {

  public ConstructorRewriter(ProgramUnit source) {
    super(source);
  }

  public void visit(MethodInvokation e){
    if (e.getDefinition()==null){
      Warning("method invokation (%s) without definition from %s",e.method.getName(),e.method.getOrigin());
    } else if (e.getDefinition().kind==Method.Kind.Constructor) {
      Fail("%s cannot deal with instantiation that is not an assignment at %s",getClass(),e.getOrigin());
    }
    super.visit(e);
  }
  
  public void visit(AssignmentStatement e){
    if (e.getExpression() instanceof MethodInvokation){
      MethodInvokation i=(MethodInvokation)e.getExpression();
      if (i.getDefinition().kind==Method.Kind.Constructor) {
        ASTNode s1=create.assignment(rewrite(e.getLocation()),create.expression(StandardOperator.New,rewrite(i.getType())));
        ASTNode s2=create.invokation(rewrite(e.getLocation()),false ,create.method_name(i.method+"_init"),rewrite(i.getArgs()));
        result=create.block(s1,s2);
        return;
      }
    }
    super.visit(e);
  }
  
  public void visit(Method m){
    if (m.kind==Method.Kind.Constructor){
      String name=m.getName()+"_init";
      DeclarationStatement args[]=rewrite(m.getArgs());
      ASTNode body=rewrite(m.getBody());
      ContractBuilder cb=new ContractBuilder();
      Contract c=m.getContract();
      if (c!=null){
        rewrite(c,cb);
        //cb.requires(rewrite(c.pre_condition));
        for(DeclarationStatement field:((ASTClass)m.getParent()).dynamicFields()){
          cb.requires(create.expression(
              StandardOperator.Perm,
              create.field_name(field.getName()),
              create.constant(100)
          ));
        }
        //cb.ensures(rewrite(c.post_condition));
      }
      result=create.method_decl(create.primitive_type(PrimitiveType.Sort.Void), cb.getContract(), name, args, body);
    } else {
      super.visit(m);
    }
  }
}
