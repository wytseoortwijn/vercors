package vct.col.rewrite;

import java.util.ArrayList;

import vct.col.ast.*;

/**
 * This rewriter converts a program with classes into
 * a program with records.
 * 
 * 
 * @author Stefan Blom
 *
 */
public class ClassConversion extends AbstractRewriter {

  public ClassConversion(ProgramUnit source) {
    super(source);
  }

  @Override
  public void visit(NameExpression e){
    if (e.isReserved(ASTReserved.This)){
      result=create.unresolved_name("this");
    } else {
      super.visit(e);
    }
  }
  @Override
  public void visit(ASTClass cl){
    ASTClass res=create.ast_class(cl.name, ASTClass.ClassKind.Record, null, null);
    if (cl.getStaticCount()>0){
      Fail("class conversion cannot be used for static entries yet.");
    }
    for(DeclarationStatement decl:cl.dynamicFields()){
      res.add(rewrite(decl));
    }
    for(Method m:cl.dynamicMethods()){
      create.enter();
      create.setOrigin(m.getOrigin());
      Method.Kind kind=m.kind;
      Type returns;
      if (m.kind==Method.Kind.Constructor){
        returns=create.class_type(cl.name);
      } else {
        returns=rewrite(m.getReturnType());
      }
      Contract contract=rewrite(m.getContract());
      String name=cl.name+"::"+m.name;
      ArrayList<DeclarationStatement> args=new ArrayList();
      if (m.kind!=Method.Kind.Constructor){
        args.add(create.field_decl("this",create.class_type(cl.name)));
      }
      for(DeclarationStatement d:m.getArgs()){
        args.add(rewrite(d));
      }
      ASTNode body=rewrite(m.getBody());
      if (m.kind==Method.Kind.Constructor){
        body=create.block(
            create.field_decl("this",create.class_type(cl.name)),
            create.assignment(
                create.local_name("this"),
                create.expression(StandardOperator.New,create.class_type(cl.name))
            ),
            body,
            create.return_statement(create.local_name("this"))
        );
      }
      boolean varArgs=m.usesVarArgs();
      Method p=create.method_kind(kind, returns, contract, name, args.toArray(new DeclarationStatement[0]), varArgs, body);
      create.leave();
      p.setStatic(true);
      target().add(p);
    }
    result=res;
  }
  
  @Override
  public void visit(MethodInvokation s){
    String method;
    ArrayList<ASTNode> args=new ArrayList();
    if (s.object instanceof ClassType){
      method=((ClassType)s.object).getName()+"::"+s.method;
    } else if (s.object==null){
      method=s.method;
    } else {
      method=((ClassType)s.object.getType()).getName()+"::"+s.method;
      args.add(rewrite(s.object));
    }
    for(ASTNode arg :s.getArgs()){
      args.add(rewrite(arg));
    }
    result=create.invokation(null, s.dispatch, method, args.toArray(new ASTNode[0]));
  }
}
