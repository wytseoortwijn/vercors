// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.java.printer;

import hre.ast.TrackingOutput;
import hre.ast.TrackingTree;
import java.io.PrintStream;
import vct.col.ast.*;
import vct.col.ast.PrimitiveType.Sort;
import vct.util.*;
import static hre.System.Abort;

/** 
 * This class contains a pretty printer for Java code.
 * 
 * @author Stefan Blom
 * 
 */
public class JavaPrinter extends AbstractPrinter {
  public JavaPrinter(TrackingOutput out){
    super(JavaSyntax.get(),out);
  }

  public void visit(ClassType t){
    out.print(t.getFullName());
  }
  
  public void visit(BindingExpression e){
    switch(e.binder){
      case FORALL:
      {
        setExpr();
        out.printf("(\\forall ");
        int N=e.getDeclCount();
        if (N!=1) Abort("cannot deal with multiple variables in binder (yet)");
        DeclarationStatement decl=e.getDeclaration(0);
        decl.getType().accept(this);
        out.printf(" %s;",decl.getName());
        e.select.accept(this);
        out.printf(";");
        e.main.accept(this);
        out.printf(")");
        return;
      }
      default:
        Abort("binder %s unimplemented",e.binder);
    }
  }
  
  public void visit(BlockStatement block){
    out.lnprintf("{");
    out.incrIndent();
    int N=block.getLength();
    for(int i=0;i<N;i++){
      block.getStatement(i).accept(this);
    }
    out.decrIndent();
    out.lnprintf("}");
  }

  public void visit(ASTClass cl){
    int N;
    switch(cl.kind){
    case Plain:
      out.lnprintf("class %s",cl.getName());
      break;
    case Abstract:
      out.lnprintf("abstract class %s",cl.getName());
      break;
    case Interface:
      out.lnprintf("interface %s",cl.getName());
      break;
    default:
      Abort("unexpected class kind %s",cl.kind);
    }
    if (cl.super_classes.length>0) {
      out.printf("  extends %s",cl.super_classes[0]);
      for(int i=1;i<cl.super_classes.length;i++){
        out.printf(", %s",cl.super_classes[i]);
      }
      out.lnprintf("");
    }
    if (cl.implemented_classes.length>0) {
      out.printf("  implements %s",cl.implemented_classes[0]);
      for(int i=1;i<cl.implemented_classes.length;i++){
        out.printf(", %s",cl.implemented_classes[i]);
      }
      out.lnprintf("");
    }
    out.lnprintf("{");
    out.incrIndent();
    N=cl.getStaticCount();
    for(int i=0;i<N;i++){
      if (cl.getStatic(i) instanceof DeclarationStatement) out.printf("static ");
      else out.println("/* static */");
      cl.getStatic(i).accept(this);
    }
    N=cl.getDynamicCount();
    for(int i=0;i<N;i++){
      cl.getDynamic(i).accept(this);
    }
    out.decrIndent();
    out.lnprintf("}");    
  }

  public void visit(DeclarationStatement s){
    ASTNode expr=s.getInit();
    nextExpr();
    s.getType().accept(this);
    out.printf(" %s",s.getName());
    if (expr!=null){
      out.printf("=");
      nextExpr();
      expr.accept(this);
    }
    out.lnprintf(";");
  }

  public void visit(Instantiation s){
    int N=s.getArity();
    setExpr();
    out.printf("(new ");
    s.getSort().accept(this);
    out.printf("(");
    if (N>0) {
      s.getArg(0).accept(this);
      out.printf(",");
      for(int i=1;i<N;i++){
        s.getArg(i).accept(this);
      }
    }
    out.printf("))");
  }

  public void visit(Method m){
    FunctionType t=m.getType();
    int N=t.getArity();
    Type result_type=t.getResult();
    String name=m.getName();
    Contract contract=m.getContract();
    boolean predicate=m.getKind()==Method.Kind.Predicate;
    if (predicate){
      if (contract!=null) {
        out.lnprintf("//ignoring contract of predicate");
        System.err.println("ignoring contract of predicate"); 
      }
      out.lnprintf("/*@");
      out.incrIndent();
      out.print("predicate ");
    }
    if (contract!=null && !predicate){
      out.lnprintf("/*@");
      out.incrIndent();
      out.printf("requires ");
      nextExpr();
      contract.pre_condition.accept(this);
      out.lnprintf(";");
      out.printf("ensures ");
      nextExpr();
      contract.post_condition.accept(this);
      out.lnprintf(";");
      if (contract.modifies!=null){
        out.printf("modifies ");
        if (contract.modifies.length==0){
          out.lnprintf("\\nothing;");
        } else {
          nextExpr();
          contract.modifies[0].accept(this);
          for(int i=1;i<contract.modifies.length;i++){
            out.printf(", ");
            nextExpr();
            contract.modifies[i].accept(this);
          }
          out.lnprintf(";");
        }
      }
      out.decrIndent();
      if (!predicate) out.lnprintf("@*/");
    }
    if (m.isStatic()) out.printf("static ");
    if (((ASTClass)m.getParent()).getName().equals(name)){
      out.printf("/*constructor*/");
    } else {
      result_type.accept(this);
    }
    out.printf(" %s(",name);
    if (N>0) {
      t.getArgument(0).accept(this);
      out.printf(" %s",m.getArgument(0));
      for(int i=1;i<N;i++){
        out.printf(",");
        t.getArgument(i).accept(this);
        out.printf(" %s",m.getArgument(i));
      }
    }
    out.printf(")");
    ASTNode body=m.getBody();
    if (body==null) {
      out.lnprintf(";");
    } else if (body instanceof BlockStatement) {
      body.accept(this);
    } else {
      out.printf("=");
      nextExpr();
      body.accept(this);
      out.lnprintf(";");
    }
    if (predicate){
      out.decrIndent();
      out.lnprintf("*/");
    }
  }

  public void visit(IfStatement s){
    int N=s.getCount();
    out.printf("if (");
    nextExpr();
    s.getGuard(0).accept(this);
    out.lnprintf("){");
    out.incrIndent();
    s.getStatement(0).accept(this);
    out.decrIndent();
    out.lnprintf("}");
    for(int i=1;i<N;i++){
      if (i==N-1 && s.getGuard(i)==IfStatement.else_guard){
        out.lnprintf(" else {");
      } else {
        out.printf(" else if (");
        nextExpr();
        s.getGuard(i).accept(this);
        out.lnprintf("){");
      }
      out.incrIndent();
      s.getStatement(i).accept(this);
      out.decrIndent();
      out.lnprintf("}");
    }
    out.lnprintf("");
  }

  public void visit(AssignmentStatement s){
    setExpr();
    s.getLocation().accept(this);
    out.printf("=");
    s.getExpression().accept(this);
    out.lnprintf(";");
  }
  public void visit(ReturnStatement s){
    ASTNode expr=s.getExpression();
    if (expr==null){
      out.lnprintf("return;");
    } else {
      out.printf("return ");
      setExpr();
      expr.accept(this);
      out.lnprintf(";");
    }
  }
  public void visit(OperatorExpression e){
    switch(e.getOperator()){
      case Fork:{
        ASTNode thread=e.getArg(0);
        String name;
        if (thread instanceof NameExpression){
          name=((NameExpression)thread).toString();
        } else {
          throw new Error("fork/join are limited to name expressions");
        }
        out.lnprintf("Thread thread_%s := new Thread(%s).start();",name,name);
        break;
      }
      case Join:{
        ASTNode thread=e.getArg(0);
        String name;
        if (thread instanceof NameExpression){
          name=((NameExpression)thread).toString();
        } else {
          throw new Error("fork/join are limited to name expressions");
        }
        out.lnprintf("thread_%s.join();",name);
        break;
      }
      case Assert:{
        out.printf("assert ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        out.lnprintf(";");
        break;
      }
      case Assume:{
        out.printf("assume ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        out.lnprintf(";");
        break;
      }
      case HoareCut:{
          out.printf("/*{ ");
          current_precedence=0;
          setExpr();
          ASTNode prop=e.getArg(0);
          prop.accept(this);
          out.lnprintf(" }*/");
          break;    	  
      }
      case Lock:{
        ASTNode lock=e.getArg(0);
        setExpr();
        lock.accept(this);
        out.lnprintf(".lock()");
        break;        
      }
      case Unlock:{
        ASTNode lock=e.getArg(0);
        setExpr();
        lock.accept(this);
        out.lnprintf(".unlock()");
        break;        
      }
      case Unfold:{
        out.printf("//@ unfold ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        out.lnprintf(";");
        break;
      }
      case Fold:{
        out.printf("//@ fold ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        out.lnprintf(";");
        break;
      }
      default:{
        super.visit(e);
      }
    }
  }

  public void visit(LoopStatement s){
    if (s.getInitBlock()!=null) throw new Error("cannot do init blocks yet.");
    if (s.getUpdateBlock()!=null) throw new Error("cannot do update blocks yet.");
    for(ASTNode inv:s.getInvariants()){
      out.printf("/*@ loop_invariant ");
      nextExpr();
      inv.accept(this);
      out.lnprintf("; */");
    }
    ASTNode tmp;
    tmp=s.getEntryGuard();
    if (tmp==null) {
      out.printf("do");
    } else {
      out.printf("while(");
      nextExpr();
      tmp.accept(this);
      out.printf(")");
    }
    tmp=s.getBody();
    if (!(tmp instanceof BlockStatement)) { out.printf(" "); }
    tmp.accept(this);
    tmp=s.getExitGuard();
    if (tmp!=null){
      out.printf("while(");
      nextExpr();
      tmp.accept(this);
      out.lnprintf(")");      
    }
  }

  public static TrackingTree dump(PrintStream out,ASTClass program){
    System.err.println("Dumping Java code...");
    try {
      TrackingOutput track_out=new TrackingOutput(out,false);
      JavaPrinter printer=new JavaPrinter(track_out);
      String name=program.getName();
      if (name==null){
        System.err.println("multiple class program");
        int N=program.getStaticCount();
        for(int i=0;i<N;i++){
          program.getStatic(i).accept(printer);
        }
      } else {
        System.err.println("single class");
        program.accept(printer);
      }
      return track_out.close();
    } catch (Exception e) {
      System.out.println("error: ");
      e.printStackTrace();
      throw new Error("abort");
    }
  }
}

