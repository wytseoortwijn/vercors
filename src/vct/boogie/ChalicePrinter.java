// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.boogie;

import hre.ast.TrackingOutput;
import vct.col.ast.*;
import vct.col.ast.PrimitiveType.Sort;
import static hre.System.Abort;
import static hre.System.Debug;

/**
 * This class contains the pretty printer for Chalice code, which is
 * based on the abstract Boogie pretty printer.
 * 
 * @author Stefan Blom
 *
 */
public class ChalicePrinter extends AbstractBoogiePrinter {

  boolean in_class=false;
  public ChalicePrinter(TrackingOutput out){
    super(BoogieSyntax.getChalice(),out);
  }
  
  public void visit(ClassType t){
    out.print(t.getName());
  }
  public void visit(PrimitiveType t){
    switch (t.sort){
    case Fraction:
      out.printf("int");
      break;
    default:
      super.visit(t);
    }
  }

  public void visit(ASTClass c){
    String class_name=c.getName();
    if (in_class) throw new Error("illegal nested class "+class_name);
    if (c.getStaticCount()>0) throw new Error("illegal static entries in "+class_name);
    in_class=true;
    String long_name[]=c.getFullName();
    out.printf("class %s",long_name[0]);
    for(int i=1;i<long_name.length;i++){
      out.printf("__%s",long_name[i]);
    }
    out.lnprintf(" {");
    out.incrIndent();
    int N=c.getDynamicCount();
    for(int i=0;i<N;i++) c.getDynamic(i).accept(this);
    out.decrIndent();
    out.lnprintf("}//end class %s",class_name);
    in_class=false;
  }

  private void print_arguments(Method m,boolean function){
    FunctionType t=m.getType();
    int N=t.getArity();
    Type result_type=t.getResult();
    Contract contract=m.getContract();
    out.printf("(");
    String next="";
    if (contract !=null) {
      for(int i=0;i<contract.given.length;i++){
        out.printf("%s%s: ",next,contract.given[i].getName());
        contract.given[i].getType().accept(this);
        next=",";
      }
    }    
    for(int i=0;i<N;i++){
      out.printf("%s%s: ",next,m.getArgument(i));
      t.getArgument(i).accept(this);
      next=",";
    }
    if (function) {
      out.printf("):");
      result_type.accept(this);
      out.lnprintf("");
    } else {
      out.printf(") returns (");
      next="";
      if (contract !=null) {
        for(int i=0;i<contract.yields.length;i++){
          out.printf("%s%s: ",next,contract.yields[i].getName());
          contract.yields[i].getType().accept(this);
          next=",";
        }
      }
      if (result_type.equals(Sort.Void)){
        out.lnprintf(")");
      } else {
        out.printf("%s__result: ",next);
        result_type.accept(this);
        out.lnprintf(")");
      }
    }
  }
  public void visit(Method m){
    String name=m.getName();
    Method.Kind kind=m.getKind();
    FunctionType t=m.getType();
    int N=t.getArity();
    Contract contract=m.getContract();
    if (N>0 && kind==Method.Kind.Predicate){
      kind=Method.Kind.Pure;
    }
    ASTNode body=m.getBody();
    Debug("method %s of kind %s", name, kind);
    switch(kind){
      case Constructor:{
        out.printf("method %s",name);
        print_arguments(m,false);
        out.lnprintf("  requires true; // should be access to variables");
        if (contract!=null) visit(contract,false);
        body.accept(this);        
        break;
      }
      case Predicate:{
        out.lnprintf("predicate %s",name);
        // no arguments allowed for predicate!
        out.lnprintf("{");
        out.incrIndent();
        in_clause=true;
        nextExpr();
        body.accept(this);
        out.decrIndent();
        out.lnprintf("");
        out.lnprintf("}");
        in_clause=false;
        break;
      }
      case Pure:{
        out.printf("function %s",name);
        print_arguments(m,true);
        if (contract!=null) visit(contract,true);
        out.lnprintf("{");
        out.incrIndent();
        in_clause=true;
        if (contract!=null && contract.pre_condition!=ContractBuilder.default_true) {
          // this is an unsafe trick!
          out.printf("unfolding ");
          nextExpr();
          current_precedence=0;
          contract.pre_condition.accept(this);
          out.printf(" in ");
        }
        nextExpr();
        body.accept(this);
        out.decrIndent();
        out.lnprintf("");
        out.lnprintf("}");
        in_clause=false;
        break;
      }
      case Plain:{
        out.printf("method %s",name);
        print_arguments(m,false);
        if (contract!=null) visit(contract,false);
        if (body==null){
          out.lnprintf("{ assume false ; /* skip body check for abstract method. */ }");
        } else {
          body.accept(this);
        }
        break;
      }
    }
  }
  public void visit(OperatorExpression e){
    switch(e.getOperator()){
    case Fold:{
      if (in_expr) throw new Error("fold is a statement");
      in_clause=true;
      out.printf("fold ");
      current_precedence=0;
      setExpr();
      ASTNode prop=e.getArg(0);
      prop.accept(this);
      out.lnprintf(";");
      in_clause=false;
      break;
    }
    case Unfold:{
      if (in_expr) throw new Error("unfold is a statement");
      in_clause=true;
      out.printf("unfold ");
      current_precedence=0;
      setExpr();
      ASTNode prop=e.getArg(0);
      prop.accept(this);
      out.lnprintf(";");
      in_clause=false;
      break;
    }
    case Fork:{
      assert !in_expr;
      ASTNode thread=e.getArg(0);
      String name;
      if (thread instanceof NameExpression){
        name=((NameExpression)thread).toString();
      } else {
        throw new Error("fork/join are limited to name expressions");
      }
      out.lnprintf("fork tok_%s := %s.run();",name,name);
      break;
    }
      case Join:{
        assert !in_expr;
        ASTNode thread=e.getArg(0);
        String name;
        if (thread instanceof NameExpression){
          name=((NameExpression)thread).toString();
        } else {
          throw new Error("fork/join are limited to name expressions");
        }
        out.lnprintf("join tok_%s;",name);
        break;
      }
      /*
      case Perm:{
        assert in_expr;
        ASTNode a0=e.getArg(0);
        ASTNode a1=e.getArg(1);
        out.print("acc(");
        a0.accept(this);
        out.print(",100*");
        a1.accept(this);
        out.print(")");
        break;
      }
      */
      case PointsTo:{
        assert in_expr;
        ASTNode a0=e.getArg(0);
        ASTNode a1=e.getArg(1);
        ASTNode a2=e.getArg(2);
        out.print("(acc(");
        current_precedence=0;
        a0.accept(this);
        out.print(",");
        current_precedence=0;
        a1.accept(this);
        out.print(") && ");
        current_precedence=syntax.getPrecedence(StandardOperator.EQ);
        a0.accept(this);
        out.print("==");
        current_precedence=syntax.getPrecedence(StandardOperator.EQ);
        a2.accept(this);
        out.print(")");
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

  public void visit(Instantiation e){
    throw new Error("instantiation is limited to right-hand side of an assignment!");
  }

  public void visit(AssignmentStatement s){
    if (in_expr) throw new Error("assignment is a statement in chalice");
    ASTNode expr=s.getExpression();
    if (expr instanceof Instantiation){
      Instantiation e=(Instantiation)expr;
      ASTNode name=e.getSort();
      setExpr();
      s.getLocation().accept(this);
      out.printf(" := new ");
      name.accept(this);
      out.lnprintf(";");
      if (e.getArity()>0){
        Abort("Chalice does not allow instantiation with arguments");
      }
    } else {
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
  }
  public void visit(MethodInvokation e){
    int N=e.getArity();
    // TODO: check site rather than rely on N==0 assumption.
    if (in_clause && N==0) {
      Debug("invokation kind is %s", e.method.getKind());
      if (e.object!=null) {
        e.object.accept(this);
        out.print(".");
      }
      e.method.accept(this);
    } else {
      super.visit(e);
    }
  }

}
