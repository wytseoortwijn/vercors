// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.util;

import hre.ast.TrackingOutput;
import java.util.*;
import vct.col.ast.*;
import vct.util.Syntax.Associativity;
import static hre.System.*;

/**
 * This class contains the generic code for pretty printing expressions
 * based on a given syntax.
 * 
 * This class will use the precedences supplied by the syntax to minimize the
 * number of parenthesis.
 * 
 * @author sccblom
 *
 */
public class AbstractPrinter extends AbstractVisitor {

  protected Syntax syntax;
  protected int current_precedence;
  protected TrackingOutput out;
  protected boolean in_expr;
  protected int expr_level;

  // use expression mode until exit from current visit
  public void setExpr(){
    if (!in_expr){
      in_expr = true;
      expr_level=1;
    }
  }
  // use inline mode in next accept call
  public void nextExpr(){
    if (!in_expr){
      in_expr = true;
      expr_level=0;
    }
  }
   
  public void pre_visit(ASTNode node){
    super.pre_visit(node);
    if (in_expr) {
      expr_level++;
    }
    if (node.getOrigin()==null){
      throw new Error("found "+node.getClass()+" without origin");
    }
    out.enter(node.getOrigin());
  }

  public void post_visit(ASTNode node){
    out.leave(node.getOrigin());
    if (in_expr) {
      expr_level--;
      in_expr=(expr_level>0);
    }
    super.post_visit(node);
  }

  public AbstractPrinter(Syntax syntax,TrackingOutput out){
    this.syntax=syntax;
    this.out=out;
    current_precedence=0;
  }

  public void visit(PrimitiveType t){
    String s=syntax.getPrimitiveType(t.sort);
    if (s==null) throw new Error("unsupported primitive type: "+t.sort);
    out.printf(s);
  }

  public void visit(NameExpression e){
    boolean statement=!in_expr;
    setExpr();
    String s=e.toString();
    out.print(s);
    if (statement) {
      out.lnprintf(";");
    }
  }

  public void visit(MethodInvokation e){
    boolean statement=!in_expr;
    setExpr();
    String i_syntax[]=syntax.getSyntax(e.guarded?StandardOperator.GuardedSelect:StandardOperator.Select);
    if (e.object!=null) {
      // TODO: manage precedence properly.
      out.printf(i_syntax[0]);
      e.object.accept(this);
      out.printf(i_syntax[1]);
    }
    e.method.accept(this);
    out.print("(");
    int N=e.getArity();
    if(N>0){
      int precedence=current_precedence;
      current_precedence=0;
      e.getArg(0).accept(this);
      for(int i=1;i<N;i++){
        out.print(",");
        current_precedence=0;
        e.getArg(i).accept(this);
      }
      current_precedence=precedence;
    }
    out.print(")");
    if (e.object!=null) {
      out.printf(i_syntax[2]);
    }
    if (statement) {
      out.lnprintf(";");
    }
  }

  public void visit(OperatorExpression e){
    StandardOperator op=e.getOperator();
    String op_syntax[]=syntax.getSyntax(op);
    if (op_syntax==null){
      throw new Error("no syntax defined for "+op+" operation");
    }
    int N=op.arity();
    int precedence=current_precedence;
    setExpr();
    if (syntax.isOperator(op)){
      int op_precedence=syntax.getPrecedence(op);
      if (op_precedence < precedence){
        out.print("(");
      }
      for(int i=0;i<N;i++){
        out.print(op_syntax[i]);
        if (i==0 && syntax.getAssociativity(op)==Associativity.Left
          ||i==(N-1) && syntax.getAssociativity(op)==Associativity.Right
        ){
          current_precedence=op_precedence;
        } else {
          current_precedence=op_precedence+1;
        }
        e.getArg(i).accept(this);
      }
      out.print(op_syntax[N]);
      if (op_precedence < precedence){
        out.print(")");
      }
    } else {
      current_precedence=0;
      for(int i=0;i<N;i++){
        out.print(op_syntax[i]);
        e.getArg(i).accept(this);
      }
      out.print(op_syntax[N]);
    }
    current_precedence=precedence;
  }

  public void visit(ConstantExpression ce){
    if (!in_expr) Abort("constant %s outside of expression for %s",ce,ce.getOrigin());
    out.print(ce.toString());
  }
}

