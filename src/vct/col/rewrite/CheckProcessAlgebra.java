package vct.col.rewrite;

import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.*;

public class CheckProcessAlgebra extends AbstractRewriter {

  public CheckProcessAlgebra(ProgramUnit source) {
    super(source);
  }

  
  @Override
  public void visit(Method m){
    if (m.getReturnType().isPrimitive(Sort.Process)){
      Contract c=m.getContract();
      ContractBuilder cb = new ContractBuilder();
      for (ASTNode v:c.modifies){
        create.enter();
        create.setOrigin(v.getOrigin());
        cb.requires(create.expression(StandardOperator.Perm,rewrite(v),create.constant(100)));
        cb.ensures(create.expression(StandardOperator.Perm,rewrite(v),create.constant(100)));
        create.leave();
      }
      if (c.pre_condition!=null) cb.requires(rewrite(c.pre_condition));
      if (c.post_condition!=null) cb.ensures(rewrite(c.post_condition));
      DeclarationStatement args[]=rewrite(m.getArgs());
      BlockStatement body=null;
      ASTNode m_body=m.getBody();
      if (m_body!=null){
        create.enter();
        body=create(m_body).block();
        create_body(body,false,m_body);
        create.leave();
      }
      result=create.method_decl(create.primitive_type(Sort.Void), cb.getContract(), m.name, args, body);
    } else {
      super.visit(m);
    }
  }


  private void create_body(BlockStatement body,boolean guarded, ASTNode m_body) {
    create.enter();
    create.setOrigin(m_body.getOrigin());
    if (m_body instanceof OperatorExpression) {
      OperatorExpression e=(OperatorExpression)m_body;
      switch(e.getOperator()){
      case ITE:{
        BlockStatement lhs=create.block();
        create_body(lhs,guarded,e.getArg(1));
        BlockStatement rhs=create.block();
        create_body(rhs,guarded,e.getArg(2));
        body.add(create.ifthenelse(rewrite(e.getArg(0)),lhs,rhs));
        break;
      }
      case Mult:{
        create_body(body,guarded,e.getArg(0));
        create_body(body,true,e.getArg(1));
      }
      case Or:{
        if (guarded){
          create.expression(StandardOperator.Assume,create.constant(false));
        } else {
          BlockStatement lhs=create.block();
          create_merge(lhs,e.getArg(0),e.getArg(1));
          BlockStatement rhs=create.block();
          create_merge(lhs,e.getArg(1),e.getArg(0));
          body.add(create.ifthenelse(rewrite(create.reserved_name(ASTReserved.Any)),lhs,rhs));
        }
      }
      default:
        Warning("skipping unknown process operator %s",e.getOperator());
      }
    } else if (m_body instanceof MethodInvokation) {
      body.add(rewrite(m_body));
    } else {
      Abort("unknown process %s",m_body.getClass());
    }
    create.leave();
  }


  private void create_merge(BlockStatement lhs, ASTNode arg, ASTNode arg2) {
    if (arg.isa(StandardOperator.Mult)){
      OperatorExpression e=(OperatorExpression)arg;
      create_body(lhs,false,e.getArg(0));
      create_body(lhs,true,e.getArg(1));
    } else if (arg instanceof MethodInvokation) {
      create.expression(StandardOperator.Assume,create.constant(false));
    } else {
      Abort("unknown merge process %s",arg.getClass());
    }
  }
}
