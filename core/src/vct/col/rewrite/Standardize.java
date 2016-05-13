package vct.col.rewrite;

import vct.col.ast.ASTNode;
import vct.col.ast.ASTReserved;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.AxiomaticDataType;
import vct.col.ast.BlockStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.NameExpression.Kind;
import vct.col.ast.OperatorExpression;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.util.ClassName;
import static hre.System.Debug;

/**
 * Standardize the representation of programs.
 * 
 * <UL>
 * <LI> Replace assignment expressions used as statements by assignment statements.
 * <LI> Replace simple increment and decrement statements by assignments.
 * <LI> Create objects for method invokations that do not have them.
 * </UL>
 * 
 * @author Stefan Blom
 *
 */
public class Standardize extends AbstractRewriter {

  public Standardize(ProgramUnit source) {
    super(source,true);
  }

  /*
  public void visit(BlockStatement s) {
    Debug("rewriting block");
    BlockStatement res=create.block();
    int N=s.getLength();
    for (int i=0;i<N;i++){
      ASTNode statement=s.getStatement(i);
      if (statement instanceof OperatorExpression) {
        OperatorExpression e=(OperatorExpression)statement;
        switch(e.getOperator()){
        case Assign:
        {
          ASTNode var=e.getArg(0).apply(this);
          ASTNode val=e.getArg(1).apply(this);
          res.add_statement(create(e.getOrigin()).assignment(var,val));
          break;
        }
        case PostIncr:
        case PreIncr:
        {
          ASTNode arg=e.getArg(0);
          if (arg instanceof NameExpression){
            ASTNode incr=create.expression(e.getOrigin(),StandardOperator.Plus,rewrite(arg),create.constant(e.getOrigin(),1));
            res.add_statement(create(e.getOrigin()).assignment(rewrite(arg),incr));
          } else {
            res.add_statement(rewrite(e));
          }
          break;
        }
        case PostDecr:
        case PreDecr:
        {
          ASTNode arg=e.getArg(0);
          if (arg instanceof NameExpression){
            ASTNode incr=create.expression(e.getOrigin(),StandardOperator.Minus,rewrite(arg),create.constant(e.getOrigin(),1));
            res.add_statement(create(e.getOrigin()).assignment(rewrite(arg),incr));
          } else {
            res.add_statement(rewrite(e));
          }
          break;
        }
        default:
          res.add_statement(statement.apply(this));
          break;
        }
      } else {
        res.add_statement(statement.apply(this));
      }
    }
    result=res;
  }
*/
  
  
  public void visit(MethodInvokation e){
    ASTNode object=rewrite(e.object);
    if(object==null){
      Method m=source().find_adt(e.method);
      if (m!=null){
        String adt=((AxiomaticDataType)m.getParent()).name;
        //System.err.printf("%s is an ADT method from %s%n", e.method,);
        //object=create.name(Kind.ADT, null,adt);
        object=create.class_type(adt);
      }
    }
    if (object==null){
      if (e.method.equals(Method.JavaConstructor)){
        object=null;
      } else if (current_class()!=null) {
        object=create.this_expression(create.class_type(current_class().getFullName()));
      }
    }
    MethodInvokation res=create.invokation(object, rewrite(e.dispatch), e.method, rewrite(e.getArgs()));
    res.set_before(rewrite(e.get_before()));
    res.set_after(rewrite(e.get_after()));
    result=res;
  }

  public void visit(NameExpression e){
    switch(e.getKind()){
      case Field:{
        Method m=current_method();
        if (m==null) {
          Fail("cannot support expressions outside of method definitions yet.");
        }
        if (m.isStatic()){
          result=create.dereference(create.class_type(current_class().getFullName()),e.getName());
        } else {
          result=create.dereference(create.reserved_name(ASTReserved.This),e.getName());
        }
        break;
      }
      case Unresolved:{
        String name=e.getName();
        ClassName cl_name=new ClassName(name);
        if (source().find(cl_name)!=null){
          result=create.class_type(name);
          break;
        }
        VariableInfo info=variables.lookup(name);
        if (info!=null) {
          Debug("unresolved %s name %s found during standardize",info.kind,name);
          e.setKind(info.kind);
        }
        super.visit(e);
        break;
      }
      default:{
        super.visit(e);
        break;
      }
    }
  }
  
  @Override
  public void visit(OperatorExpression e){
    if (e.getParent() instanceof BlockStatement){
      switch(e.getOperator()){
      case Assign:
      {
        ASTNode var=e.getArg(0).apply(this);
        ASTNode val=e.getArg(1).apply(this);
        result=create.assignment(var,val);
        break;
      }
      case PostIncr:
      case PreIncr:
      {
        ASTNode arg=e.getArg(0);
        if (arg instanceof NameExpression){
          ASTNode incr=create.expression(e.getOrigin(),StandardOperator.Plus,rewrite(arg),create.constant(e.getOrigin(),1));
          result=create.assignment(rewrite(arg),incr);
        } else {
          super.visit(e);
        }
        break;
      }
      case PostDecr:
      case PreDecr:
      {
        ASTNode arg=e.getArg(0);
        if (arg instanceof NameExpression){
          ASTNode incr=create.expression(e.getOrigin(),StandardOperator.Minus,rewrite(arg),create.constant(e.getOrigin(),1));
          result=create.assignment(rewrite(arg),incr);
        } else {
          super.visit(e);
        }
        break;
      }
      default:
        super.visit(e);
        break;
      }
    } else {
      super.visit(e);
    }
  }
}
