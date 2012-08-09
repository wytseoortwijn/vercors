package vct.col.rewrite;

import hre.ast.MessageOrigin;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTNode;
import vct.col.ast.ClassType;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.StandardOperator;
import vct.util.ClassName;
import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Fail;
import static hre.System.Warning;

/**
 * Base class for rewriting all static entries as a single Global class.
 * This base class will do all of the rewriting, except the creation
 * of the name global that refers to the global entries. The class
 * {@link GlobalizeStaticsParameter} adds a parameter global to all
 * non-static methods. The class {@link GlobalizeStaticsField} adds
 * a field global to every class.
 * 
 * An advantage of adding a field is that it allows non-static predicates
 * to refer to static variables without adding an argument.
 * A disadvantage is that it requires generating contracts to make it work.
 * 
 * @author sccblom
 *
 */
public abstract class GlobalizeStatics extends AbstractRewriter {
  
  protected ASTClass global_class;
  protected String prefix;
  protected boolean processing_static;
  
  public void visit(ASTClass cl){
    if (cl.getParent()==null){
      global_class=create.ast_class(new MessageOrigin("filtered globals"),"Global",ClassKind.Plain,null,null);
    }
    switch(cl.kind){
    case Package:{
      int N=cl.getStaticCount();
      ASTClass res;
      if (cl.getParent()==null){
        res=create.root_package();
        res.add_static(global_class);
      } else {
        res=create.sub_package(cl.name);
      }
      for(int i=0;i<N;i++){
        res.add_static(cl.getStatic(i).apply(this));
      }
      result=res;
      break;
    }
    case Plain:{
      int N;
      ASTClass res=create.ast_class(cl.name,ClassKind.Plain,null,null);
      N=cl.getStaticCount();
      prefix=new ClassName(cl.getFullName()).toString("_");
      processing_static=true;
      Debug("prefix is now %s",prefix);
      for(int i=0;i<N;i++){
        global_class.add_dynamic(cl.getStatic(i).apply(this));
      }
      prefix=null;
      processing_static=false;
      Debug("prefix is now %s",prefix);
      N=cl.getDynamicCount();
      for(int i=0;i<N;i++){
        res.add_dynamic(cl.getDynamic(i).apply(this));
      }
      result=res;
      break;      
    }
    default: Abort("missing case");
    }
  }
  public void visit(DeclarationStatement s){
    if (prefix!=null){
      String save=prefix;
      prefix=null;
      result=create.field_decl(save+"_"+s.getName(),
           rewrite_and_cast(s.getType()), 
           rewrite_nullable(s.getInit()));
      prefix=save;
    } else {
      super.visit(s);
    }
  }
  public void visit(Method m){
    if (prefix!=null){
      String save=prefix;
      prefix=null;
      result=create.method_decl(
          rewrite_and_cast(m.getReturnType()),
          rewrite(m.getContract()),
          save+"_"+m.getName(),
          rewrite_and_cast(m.getArgs()),
          rewrite(m.getBody()));
      prefix=save;
    } else {
      super.visit(m);
    }
  }

  public void visit(MethodInvokation m){
    if (m.object instanceof ClassType && !m.isInstantiation()){
      String prefix=new ClassName(((ClassType)m.object).name).toString("_");
      if (processing_static){
        result=create.invokation(
          create.this_expression(create.class_type("Global")),
          m.guarded,
          create.method_name(prefix+"_"+m.method.getName()),
          rewrite(m.getArgs()));
      } else {
        result=create.invokation(
            create.local_name("global"),
            m.guarded,
            create.method_name(prefix+"_"+m.method.getName()),
            rewrite(m.getArgs()));        
      }
    } else {
      super.visit(m);
    }
  }

  public void visit(OperatorExpression e){
    if (e.getOperator()==StandardOperator.Select && (e.getArg(0) instanceof ClassType)){
      NameExpression var=(NameExpression)e.getArg(1);
      String var_name=new ClassName(((ClassType)e.getArg(0)).name).toString("_")+"_"+var.getName();
      if (!processing_static){
        result=create.expression(
            StandardOperator.Select,
            create.local_name("global"),
            create.field_name(var_name));
      } else {
        result=create.expression(
          StandardOperator.Select,
          create.this_expression(create.class_type("Global")),
          create.field_name(var_name));
      }
    } else {
      super.visit(e);
    }
  }
}
