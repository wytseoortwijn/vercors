// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.boogie;

import hre.ast.TrackingOutput;
import vct.col.ast.*;
import vct.col.ast.PrimitiveType.Sort;
import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Fail;

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
    super(BoogieSyntax.getChalice(),out,false);
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
    DeclarationStatement args[]=m.getArgs();
    Type result_type=m.getReturnType();
    out.printf("(");
    String next="";
    for(int i=0;i<args.length;i++){
      if (args[i].isValidFlag(ASTFlags.OUT_ARG)&&args[i].getFlag(ASTFlags.OUT_ARG)) continue;
      out.printf("%s%s: ",next,args[i].getName());
      args[i].getType().accept(this);
      next=",";
    }
    if (function) {
      out.printf("):");
      result_type.accept(this);
      out.lnprintf("");
    } else {
      out.printf(") returns (");
      if (result_type.equals(Sort.Void)){
        next="";
      } else {
        out.printf("__result: ");
        result_type.accept(this);
        next=",";
      }
      for(int i=0;i<args.length;i++){
        if (args[i].isValidFlag(ASTFlags.OUT_ARG)&&args[i].getFlag(ASTFlags.OUT_ARG)) {
          out.printf("%s%s: ",next,args[i].getName());
          args[i].getType().accept(this);
          next=",";
        }
      }
      out.lnprintf(")");
    }
  }
  public void visit(Method m){
    String name=m.getName();
    Method.Kind kind=m.getKind();
    int N=m.getArity();
    Contract contract=m.getContract();
    if (contract!=null) post_condition=contract.post_condition;
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
        if (body==null) {
          out.lnprintf("function %s_abstract():bool",name);
          out.lnprintf("predicate %s { %s_abstract() }",name,name);
        } else {
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
        }
        break;
      }
      case Pure:{
        out.printf("function %s",name);
        print_arguments(m,true);
        if (contract!=null) visit(contract,true);
        if (body !=null) {
          out.lnprintf("{");
          out.incrIndent();
          in_clause=true;
          if (contract!=null && !contract.pre_condition.equals(ContractBuilder.default_true)) {
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
        } else {
          out.lnprintf("// abstract! ");
        }
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
      //TODO: fix assumed global argument!
      out.lnprintf("fork tok_%s := %s.run(global);",name,name);
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
      case Value:{
        assert in_expr;
        ASTNode a0=e.getArg(0);
        out.print("rd*(");
        //out.print("rd(");
        a0.accept(this);
        out.print(")");
        //out.print(",*)");
        break;
      }
      case New:{
        assert in_expr;
        out.print("new ");
        e.getArg(0).accept(this);
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

  public void visit(MethodInvokation e){
    int N=e.getArity();
    // TODO: check site rather than rely on N==0 assumption.
    if (in_clause && N==0 && (e.getType()==null || e.getType().isBoolean())) {
      Debug("invoking %s of kind %s",e.method,e.method.getKind());
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
