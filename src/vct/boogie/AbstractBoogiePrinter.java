// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.boogie;

import hre.ast.TrackingOutput;
import vct.col.ast.*;
import vct.util.*;
import static hre.System.Fail;


/**
 * This class contains a pretty printer for the common part of Boogie and Chalice.
 * 
 * @author Stefan Blom
 */
public abstract class AbstractBoogiePrinter extends AbstractPrinter {
  protected boolean in_clause=false;
  protected ASTNode post_condition=null;
  
  public AbstractBoogiePrinter(Syntax syntax,TrackingOutput out){
    super(syntax,out);
  }
  public void visit(MethodInvokation e){
    boolean statement=!in_expr;
    if(!in_expr) {
      out.printf("call ");
    }
    setExpr();
    super.visit(e);
    if(statement) out.lnprintf(";");
  }
  public void visit(AssignmentStatement s){
    if (in_expr) throw new Error("assignment is a statement in chalice");
    ASTNode expr=s.getExpression();
    if (expr instanceof MethodInvokation){
      out.printf("call ");
    }
    nextExpr();
    s.getLocation().accept(this);
    out.printf(" := ");
    nextExpr();
    s.getExpression().accept(this);
    out.lnprintf(";");
  }
 
  public void visit(BlockStatement s){
    out.lnprintf("{");
    out.incrIndent();
    int N=s.getLength();
    for(int i=0;i<N;i++) s.getStatement(i).accept(this);
    out.decrIndent();
    out.lnprintf("}");
  }
  
  public void visit(Contract contract){
    visit(contract,false);
  }
  
  public void visit(Contract contract,boolean function){
    in_clause=true;
    out.incrIndent();
    nextExpr();
    if (contract.pre_condition.getOrigin()==null) {
      throw new Error("pre condition has no origin");
    }
    out.printf("requires ");
    current_precedence=0;
    contract.pre_condition.accept(this);
    out.lnprintf(";");
    if(!function){
      nextExpr();
      if (contract.post_condition.getOrigin()==null) {
        throw new Error("post condition has no origin");
      }
      out.printf("ensures ");
      current_precedence=0;
      contract.post_condition.accept(this);
      out.lnprintf(";");
    }
    out.decrIndent();
    in_clause=false;
  }
  
  public void visit(PrimitiveType t){
    switch (t.sort){
    case Long:
    case Integer:
      out.printf("int");
      break;
    case Void:
      out.printf("void");
      break;
    case Boolean:
      out.printf("bool");
      break;
    default:
      Fail("Primitive type %s is not supported, please use an encoding.",t.sort);
    }
  }

  public void visit(DeclarationStatement s){
    out.printf("var %s : ",s.getName());
    nextExpr();
    s.getType().accept(this);
    out.lnprintf(";");
  }
  
  public void visit(IfStatement s){
    int N=s.getCount();
    for(int i=0;i<N;i++){
      ASTNode g=s.getGuard(i);
      ASTNode gs=s.getStatement(i);
      if(i==0) {
        out.printf("if(");
        nextExpr();
        g.accept(this);
        out.lnprintf(")");
      } else if (i==N-1 && g==IfStatement.else_guard) {
        out.lnprintf("else");
      } else {
        out.printf("else if(");
        nextExpr();
        g.accept(this);
        out.lnprintf(")");
      }
      out.incrIndent();
      gs.accept(this);
      out.decrIndent();
    }
  }

  public void visit(LoopStatement s){
    ASTNode entry_guard=s.getEntryGuard();
    ASTNode exit_guard=s.getExitGuard();
    ASTNode body=s.getBody();
    if (exit_guard!=null) throw new Error("cannot generate for exit condition yet");
    if (entry_guard!=null) {
      out.printf("while(");
      nextExpr();
      entry_guard.accept(this);
      out.lnprintf(")");
    } else {
      out.lnprintf("while(true)");
    }
    out.incrIndent();
    for(ASTNode inv:s.getInvariants()){
      out.printf("invariant ");
      nextExpr();
      inv.accept(this);
      out.lnprintf(";");
    }
    out.decrIndent();
    if (body instanceof BlockStatement) {
      body.accept(this);
    } else {
      out.lnprintf("{");
      out.incrIndent();
      body.accept(this);
      out.decrIndent();      
      out.lnprintf("}");
    }
  }
  public void visit(OperatorExpression e){
    String keyword=null;
    switch(e.getOperator()){
      case Assume:
        if (keyword==null) keyword="assume";
      case Assert:
      {
        if (keyword==null) keyword="assert";
        if (in_expr) Fail("%s is a statement",keyword);
        in_clause=true;
        out.printf("%s ",keyword);
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        out.lnprintf(";");
        in_clause=false;
        break;
      }
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
        // a1.accept(this);
        // break;
      }
      default:{
        super.visit(e);
      }
    }
  }

  public void visit(ReturnStatement s){
    if (s.getExpression()!=null) {
      out.printf("__result := ");
      nextExpr();
      s.getExpression().accept(this);
      out.lnprintf(";");
    }
    if (post_condition!=null){
      out.printf("assert ");
      nextExpr();
      in_clause=true;
      post_condition.accept(this);
      out.lnprintf(";");
      in_clause=false;
    }
    out.lnprintf("assume false; // return;");   
  }
  
}

