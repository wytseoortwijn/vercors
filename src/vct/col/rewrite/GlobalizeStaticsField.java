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
import vct.col.ast.StandardOperator;
import vct.util.ClassName;
import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Fail;
import static hre.System.Warning;

/**
 * Add the global name as a field.
 * This encoding requires a lot of contract modifications.
 * It might be deleted rather than perfected in the future. 
 *
 * @author sccblom
 *
 */
public class GlobalizeStaticsField extends GlobalizeStatics {

  /**
   * Add the global field to every class.
   */
  public void visit(ASTClass cl){
    super.visit(cl);
    if (cl.kind==ASTClass.ClassKind.Plain){
      ((ASTClass)result).add_dynamic(create.field_decl("global",create.class_type("Global")));
    }
  }

  /**
   * Extend contracts of non-static methods.
   */
  public void visit(Method m){
    if (prefix!=null){
      super.visit(m);
    } else {
      switch(m.getKind()){
      case Plain: {
        Contract c=m.getContract();
        ContractBuilder cb=new ContractBuilder();
        cb.requires(create.expression(StandardOperator.Value,create.field_name("global")));
        cb.ensures(create.expression(StandardOperator.Value,create.field_name("global")));
        for(DeclarationStatement d: m.getArgs()){
          if (d.getType() instanceof ClassType){
            ASTNode not_null=create.expression(StandardOperator.NEQ,create.local_name(d.getName()),create.reserved_name("null"));
            ASTNode gname=create.expression(StandardOperator.Select,create.local_name(d.getName()),create.field_name("global"));
            ASTNode access=create.expression(StandardOperator.Value,gname);
            ASTNode same=create.expression(StandardOperator.EQ,create.field_name("global"),gname);
            cb.requires(create.expression(StandardOperator.Implies,not_null,
                create.expression(StandardOperator.Star,access,same)));
          }
        }
        if (c!=null){
          cb.requires(rewrite(c.pre_condition));
          cb.ensures(rewrite(c.post_condition));
        }
        result=create.method_decl(
            rewrite_and_cast(m.getReturnType()),
            rewrite(cb.getContract()),
            m.getName(),
            rewrite_and_cast(m.getArgs()),
            rewrite(m.getBody()));
        break;
      }
      default:
        super.visit(m);
      }
    }
  }

  /**
   * Extend loop-invariants of non-static methods.
   */
 public void visit(LoopStatement s){
    super.visit(s);
    if (!processing_static) {
      ASTNode same=create.expression(StandardOperator.EQ,create.field_name("global"),
          create.expression(StandardOperator.Old,create.field_name("global")));
      ((LoopStatement)result).prependInvariant(same);
      ((LoopStatement)result).prependInvariant(create.expression(StandardOperator.Value,create.field_name("global")));
    }
  }

}
