// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.boogie;

import hre.ast.TrackingOutput;
import vct.col.ast.*;
import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Fail;

/**
 * This class contains a pretty printer for Boogie programs.
 * 
 * @author sccblom
 *
 */
public class BoogiePrinter extends AbstractBoogiePrinter {
  
  public BoogiePrinter(TrackingOutput out){
    super(BoogieSyntax.getBoogie(),out,true);
  }

  public void visit(Method m){
    if (m.kind==Method.Kind.Constructor) {
      Debug("skipping constructor");
      return;
    }
    DeclarationStatement args[]=m.getArgs();
    int N=args.length;
    Type result_type=m.getReturnType();
    if (!result_type.equals(PrimitiveType.Sort.Void)) Fail("illegal return type %s",result_type);
    String name=m.getName();
    //TODO:
    //if (result_type.equals("pred")){
    //  throw new Error("Boogie does not allow predicates");
    //}
    out.printf("procedure %s(",name);
    String next="";
    for(int i=0;i<N;i++){
      if (args[i].isValidFlag(ASTFlags.OUT_ARG)&&args[i].getFlag(ASTFlags.OUT_ARG)) continue;
      out.printf("%s%s: ",next,args[i].getName());
      args[i].getType().accept(this);
      next=",";
    }
    out.printf(") returns (");
    next="";
    for(int i=0;i<args.length;i++){
      if (args[i].isValidFlag(ASTFlags.OUT_ARG)&&args[i].getFlag(ASTFlags.OUT_ARG)) {
        out.printf("%s%s: ",next,args[i].getName());
        args[i].getType().accept(this);
        next=",";
      }
    }
    out.lnprintf(")");
    Contract contract=m.getContract();
    if (contract!=null){
      visit(contract);
      post_condition=contract.post_condition;
    }
//    if (all_fields!=null){
//      out.lnprintf("modifies %s;",all_fields);
//    }
    ASTNode body=m.getBody();
    body.accept(this);
    out.lnprintf("//end procedure %s",name);
    post_condition=null;
  }
  public void visit(OperatorExpression e){
    switch(e.getOperator()){
/* this should be legacy code:
      case Select:{
        ASTNode a0=e.getArg(0);
        ASTNode a1=e.getArg(1);
        if (a0 instanceof NameExpression && a1 instanceof NameExpression){
          String s0=((NameExpression)a0).toString();
          String s1=((NameExpression)a1).toString();
          if (s0.equals("model")){
            if (s1.equals("old")){
              out.print("old");
              return;
            }
            throw new Error("unknown keyword "+s1);
          }
        }
        // Let's hope this was a this. in case of Boogie!
        a1.accept(this);
        break;
      }
*/
      case HoarePredicate:{
          Fail("Hoare Logic is not supported in this release.");
          /* TODO: solve at least two remaining problems:
           *  1. havoc'ing all variables that must be havoc'ed.
           *  2. the assume false after a return makes weakening
           *     of the last result difficult.
           */
          if (in_expr) throw new Error("Hoare Cut is a statement");
          in_clause=true;
          out.printf("assert ");
          current_precedence=0;
          setExpr();
          ASTNode prop=e.getArg(0);
          prop.accept(this);
          out.lnprintf(";");
          out.printf("assume ");
          current_precedence=0;
          setExpr();
          prop.accept(this);
          out.lnprintf(";");          
          in_clause=false;
          break;
      }
      default:{
        super.visit(e);
      }
    }
  }

  public void visit(NameExpression e){
    String s=e.toString();
    if (s.equals("\\result")){
      out.print("__result");
    } else if (s.equals("\\old")){
      out.print("old");
    } else {
      out.print(s);
    }
  }


  public void visit(ASTClass cl){
    int N=cl.getStaticCount();
    int M=cl.getDynamicCount();
    for(int i=0;i<M;i++) {
      if (cl.getDynamic(i) instanceof Method){
        Method m=(Method)cl.getDynamic(i);
        if (m.kind==Method.Kind.Constructor){
          continue;
        }
      } else if (cl.getDynamic(i) instanceof ASTSpecialDeclaration){
        ASTSpecialDeclaration s=(ASTSpecialDeclaration)cl.getDynamic(i);
        if (s.kind==ASTSpecialDeclaration.Kind.Comment){
          continue;
        }
      }
      throw new Error("illegal non-static in Boogie input");
    }
    if (N==1 && cl.getStatic(0) instanceof ASTClass){
      visit((ASTClass)cl.getStatic(0));
    } else for(int i=0;i<N;i++){
      cl.getStatic(i).accept(this);
      out.println("");
    }
  }
}
