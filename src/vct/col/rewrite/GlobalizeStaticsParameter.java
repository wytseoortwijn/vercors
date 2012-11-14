package vct.col.rewrite;

import hre.ast.MessageOrigin;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTNode;
import vct.col.ast.ClassType;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.util.ClassName;
import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Fail;
import static hre.System.Warning;

/**
 * Use a parameter global to refer to static entries.
 * 
 * @author sccblom
 *
 */
public class GlobalizeStaticsParameter extends GlobalizeStatics {

  public GlobalizeStaticsParameter(ProgramUnit source) {
    super(source);
  }

  /**
   * Add the global argument to every non-static method.
   */
  public void visit(Method m){
    if (prefix!=null){
      super.visit(m);
    } else {
      switch(m.getKind()){
      case Constructor:
      case Plain: {
        DeclarationStatement args[]=new DeclarationStatement[m.getArity()+1];
        //TODO: parameter decl in factory!
        args[0]=create.field_decl("global",create.class_type("Global"));
        for(int i=1;i<args.length;i++){
          args[i]=rewrite(m.getArgs()[i-1]);
        }
        result=create.method_kind(
            m.getKind(),
            rewrite(m.getReturnType()),
            rewrite(m.getContract()),
            m.getName(),
            args,
            rewrite(m.getBody()));
        break;
      }
      default:
        super.visit(m);
      }
    }
  }
  
  /**
   * Add the this/global argument to every invokation of a non-static method.
   */
  public void visit(MethodInvokation m){
    if (m.object instanceof ClassType && !m.isInstantiation()){
      super.visit(m);
    } else {
      Method.Kind kind=Method.Kind.Predicate;
      if (m.getDefinition()!=null){
        kind=m.getDefinition().getKind();
      } else {
        Warning("assuming kind of %s is Predicate",m.method);
      }
      switch(kind){
      case Constructor:
      case Plain:{
        ASTNode args[]=new ASTNode[m.getArity()+1];
        if (processing_static){
          args[0]=create.reserved_name("this");
        } else {
          args[0]=create.local_name("global");
        }
        for(int i=1;i<args.length;i++){
          args[i]=rewrite(m.getArg(i-1));
        }
        result=create.invokation(
            rewrite(m.object),
            m.guarded,
            m.method,
            args
        );
        break;
      }
      case Pure:
      case Predicate:
        super.visit(m);
        break;
      default:
        Abort("missing case: %s",kind);
        break;
      }
    }
  }
}

