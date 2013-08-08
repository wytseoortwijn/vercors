// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.java.printer;

import hre.ast.TrackingOutput;
import hre.ast.TrackingTree;
import java.io.PrintStream;
import vct.col.ast.*;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.util.ASTUtils;
import vct.util.*;
import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Warning;

/** 
 * This class contains a pretty printer for Java code.
 * 
 * @author Stefan Blom
 * 
 */
public class JavaPrinter extends AbstractPrinter {
  
  public JavaPrinter(TrackingOutput out){
    super(JavaSyntax.getJavaJML(),out);
  }

  public void pre_visit(ASTNode node){
    super.pre_visit(node);
    for(NameExpression lbl:node.getLabels()){
      nextExpr();
      lbl.accept(this);
      out.printf(":");
      //out.printf("[");
    }
  }
  
  public void post_visit(ASTNode node){
    if (node instanceof BeforeAfterAnnotations){
      BeforeAfterAnnotations baa=(BeforeAfterAnnotations)node;
      if (baa.get_before()!=null && baa.get_before().size()>0 || baa.get_after()!=null && baa.get_after().size()>0){
        out.printf("/*@ ");
        BlockStatement tmp=baa.get_before();
        if (tmp!=null && tmp.size()>0) {
          out.printf("with ");
          tmp.accept(this);
        }
        tmp=baa.get_after();
        if (tmp!=null && tmp.size()>0) {
          out.printf("then ");
          tmp.accept(this);      
        }
        out.printf(" */");
      }
    }
    super.post_visit(node);
  }
  /* TODO: copy to appropriate places
  public void post_visit(ASTNode node){
    if (node.get_before()!=null || node.get_after()!=null){
      out.printf("/*@ ");
      ASTNode tmp=node.get_before();
      if (tmp!=null) {
        out.printf("with ");
        tmp.accept(this);
      }
      tmp=node.get_after();
      if (tmp!=null) {
        out.printf("then ");
        tmp.accept(this);      
      }
      out.printf(" \*\/");
    }
    super.post_visit(node);
  }
  */ 
  
  @Override
  public void visit(ASTSpecial s){
    switch(s.kind){
    case Expression:
      setExpr();
      s.args[0].accept(this);
      out.println(";");
      break;
    case Assert:
      out.print("//@ assert ");
      setExpr();
      s.args[0].accept(this);
      out.println(";");
      break;
    default:
      super.visit(s);
      break;
    }
  }
  
  @Override
  public void visit(ClassType t){
    out.print(t.getFullName());
    ASTNode args[]=t.getArgs();
    if (args.length>0){
      setExpr();
      out.print("<");
      args[0].accept(this);
      for(int i=1;i<args.length;i++){
        out.print(",");
        args[i].accept(this);
      }
      out.print(">");
    }
  }
  public void visit(FunctionType t){
    int N=t.getArity();
    N--;
    for(int i=0;i<N;i++){
      t.getArgument(i).accept(this);
      out.print(",");
    }
    t.getArgument(N).accept(this);
    out.print("->");
    t.getResult().accept(this);
  }

  public void visit(BindingExpression e){
    String binder=null;
    switch(e.binder){
      case FORALL:
        binder="\\forall";
        break;
      case EXISTS:
        binder="\\exists";
        break;
      case STAR:
        binder="\\forall*";
        break;
      case LET:
        binder="\\let";
        break;
      default:
        Abort("binder %s unimplemented",e.binder);
    }
    setExpr();
    out.printf("(%s ",binder);
    int N=e.getDeclCount();
    if (N!=1) Abort("cannot deal with multiple variables in binder (yet)");
    DeclarationStatement decl=e.getDeclaration(0);
    decl.getType().accept(this);
    out.printf(" %s",decl.getName());
    if (decl.getInit()!=null){
      out.printf("= ");
      decl.getInit().accept(this);
    }
    out.printf(";");
    if (e.select!=null){
      e.select.accept(this);
      out.printf(";");
    }
    e.main.accept(this);
    out.printf(")");
  }

  public void visit(BlockStatement block){
    boolean nested=(block.getParent() instanceof IfStatement);
    if (!nested){
      if (in_expr) {
        out.printf("{");
      } else {
        out.lnprintf("{");
      }
      out.incrIndent();
    }
    int N=block.getLength();
    for(int i=0;i<N;i++){
      ASTNode statement=block.getStatement(i);
      statement.accept(this);
      if (statement instanceof LoopStatement) continue;
      if (statement instanceof DeclarationStatement) continue;
      if (statement instanceof IfStatement) continue;
      if (in_expr) {
        out.printf(";");
      } else {
        out.lnprintf(";");
      }
    }
    if (!nested) {
      out.decrIndent();
      if (in_expr) {
        out.printf("}");
      } else {
        out.lnprintf("}");
      }
    }
  }

  public void visit(ASTClass cl){
    visit(cl.getContract());
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
    case Kernel:
      out.lnprintf("kernel %s",cl.getName());
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
    for(ASTNode item:cl){
      if (item.isStatic()){
        if (item instanceof DeclarationStatement) out.printf("static ");
        else out.println("/* static */");
      }
      item.accept(this);
    }
    out.decrIndent();
    out.lnprintf("}");    
  }

  @Override
  public void visit(Contract contract) {
    if (contract!=null){
      out.lnprintf("/*@");
      out.incrIndent();
      for (DeclarationStatement d:contract.given){
        out.printf("given ");
        d.accept(this);
      }
      for(ASTNode e:ASTUtils.conjuncts(contract.pre_condition)){
        out.printf("requires ");
        nextExpr();
        e.accept(this);
        out.lnprintf(";");
      }
      for (DeclarationStatement d:contract.yields){
        out.printf("yields ");
        d.accept(this);
      }
      for(ASTNode e:ASTUtils.conjuncts(contract.post_condition)){
        out.printf("ensures ");
        nextExpr();
        e.accept(this);
        out.lnprintf(";");
      }
      for (DeclarationStatement d:contract.signals){
        out.printf("signals (");
        d.getType().accept(this);
        out.printf(" %s) ",d.getName());
        nextExpr();
        d.getInit().accept(this);
        out.lnprintf(";");
      }      
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
      out.lnprintf("@*/");
    }
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
    if (!in_expr) out.lnprintf(";");
  }

  public void visit(Method m){
    int N=m.getArity();
    Type result_type=m.getReturnType();
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
      visit(contract);
    }
    if (m.isStatic()) out.printf("static ");
    if (m.isValidFlag(ASTFlags.FINAL) && m.getFlag(ASTFlags.FINAL)){
      out.printf("final ");
    }
    if (((ASTClass)m.getParent()).getName().equals(name)){
      //out.printf("/*constructor*/");
    } else {
      result_type.accept(this);
      out.printf(" ");
    }
    out.printf("%s(",name);
    if (N>0) {
      DeclarationStatement args[]=m.getArgs();
      if (args[0].isValidFlag(ASTNode.GHOST) && args[0].isGhost()){ out.printf("/*@ ghost */"); }
      if (args[0].isValidFlag(ASTFlags.OUT_ARG) && args[0].getFlag(ASTFlags.OUT_ARG)){ out.printf("/*@ out */"); }
      m.getArgType(0).accept(this);
      if (N==1 && m.usesVarArgs()){
        out.print(" ...");
      }
      out.printf(" %s",m.getArgument(0));
      for(int i=1;i<N;i++){
        out.printf(",");
        if (args[i].isValidFlag(ASTNode.GHOST) && args[i].isGhost()){ out.printf("/*@ ghost */"); }
        if (args[i].isValidFlag(ASTFlags.OUT_ARG) && args[i].getFlag(ASTFlags.OUT_ARG)){ out.printf("/*@ out */"); }
        m.getArgType(i).accept(this);
        if (i==N-1 && m.usesVarArgs()){
          out.print(" ...");
        }
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
    if (s.isValidFlag(ASTNode.GHOST) && s.getFlag(ASTNode.GHOST)){
      int N=s.getCount();
      out.printf ("/*@ CaseSet[");
      for(int i=0;i<N;i++){
        if (i>0) out.printf ("  @         ");
        out.printf("(");
        nextExpr();
        s.getGuard(i).accept(this);
        out.printf(",");
        ASTNode n=s.getStatement(i);
        if (n instanceof BlockStatement){
          BlockStatement block=(BlockStatement)n;
          int M=block.getLength();
          for(int j=0;j<M;j++){
            if(j>0) out.printf(";");
            nextExpr();
            block.getStatement(j).accept(this);
          }
        } else {
          Abort("statement in caseset is not a block at %s",n.getOrigin());
        }
        out.printf(")");
        if(i==N-1){
          out.lnprintf("];");
        } else {
          out.lnprintf(",");
        }
      }
      out.lnprintf("  @*/");
    } else {
      int N=s.getCount();
      out.printf("if (");
      nextExpr();
      s.getGuard(0).accept(this);
      out.lnprintf("){");
      out.incrIndent();
      s.getStatement(0).accept(this);
      out.decrIndent();
      out.printf("}");
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
        out.printf("}");
      }
      out.lnprintf("");
    }
  }

  public void visit(AssignmentStatement s){
    setExpr();
    s.getLocation().accept(this);
    out.printf("=");
    s.getExpression().accept(this);
  }

  public void visit(ReturnStatement s){
    ASTNode expr=s.getExpression();
    if (expr==null){
      out.lnprintf("return");
    } else {
      out.printf("return ");
      setExpr();
      expr.accept(this);
    }
    if (s.get_after()!=null){
      out.printf("/*@ ");
      out.printf("then ");
      s.get_after().accept(this);
      out.printf(" */");
    }
  }

  public void visit(Lemma l){
      out.printf("/*@ lemma ");
      l.block.accept(this);
      out.lnprintf(" */");
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
        out.lnprintf("Thread thread_%s := new Thread(%s).start()",name,name);
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
        out.lnprintf("thread_%s.join()",name);
        break;
      }
      case Assert:{
        out.printf("assert ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case Continue:{
        out.printf("continue ");
        current_precedence=0;
        ASTNode lbl=e.getArg(0);
        if (lbl!=null){
          setExpr();
          lbl.accept(this);
        }
        break;
      }
      case Assume:{
        out.printf("assume ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case HoarePredicate:{
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
      case DirectProof:{
        out.printf("//@ proof ");
        current_precedence=0;
        setExpr();
        ASTNode string=e.getArg(0);
        string.accept(this);
        break;
      }
      case Unfold:{
        out.printf("//@ unfold ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case Fold:{
          out.printf("//@ fold ");
          current_precedence=0;
          setExpr();
          ASTNode prop=e.getArg(0);
          prop.accept(this);
          break;
        }
      case Use:{
        out.printf("//@ use ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case Access:{
        out.printf("//@ access ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case Apply:{
          out.printf("//@ apply ");
          current_precedence=0;
          setExpr();
          ASTNode prop=e.getArg(0);
          prop.accept(this);
          break;
        }
      case QED:{
          out.printf("//@ qed ");
          current_precedence=0;
          setExpr();
          ASTNode prop=e.getArg(0);
          prop.accept(this);
          break;
        }
      case Open:{
        out.printf("//@ open ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        if (e.get_before()!=null){
          out.printf(" where ");
          e.get_before().accept(this);
          if (e.get_after()!=null){
            out.printf(" then ");
            e.get_after().accept(this);
          }
        }
        break;
      }
      case Close:{
        out.printf("//@ close ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case New:{
        out.printf("new ");
        e.getArg(0).accept(this);
        out.printf("()");
        break;
      }
      case Build:{
        ASTNode args[]=e.getArguments();
        setExpr();
        out.printf("new ");
        args[0].accept(this);
        out.printf("{");
        String sep="";
        for(int i=1;i<args.length;i++){
          out.printf("%s",sep);
          sep=",";
          args[i].accept(this);
        }
        out.printf("}");
        break;
      }
      default:{
        super.visit(e);
      }
    }
  }

  public void visit(LoopStatement s){
    for(ASTNode inv:s.getInvariants()){
      out.printf("/*@ loop_invariant ");
      nextExpr();
      inv.accept(this);
      out.lnprintf("; */");
    }
    ASTNode tmp;
    if (s.getInitBlock()!=null){
      out.printf("for(");
      nextExpr();
       if(s.getInitBlock() instanceof BlockStatement)
      ((BlockStatement)s.getInitBlock()).getStatement(0).accept(this);
       else s.getInitBlock().accept(this);
      out.printf(";");
      nextExpr();
      s.getEntryGuard().accept(this);
      out.printf(";");
      if ((s.getUpdateBlock())!=null){
        nextExpr();
        if(s.getUpdateBlock() instanceof BlockStatement)
        ((BlockStatement)s.getUpdateBlock()).getStatement(0).accept(this);
        else 
        	s.getUpdateBlock().accept(this);
      }
      out.printf(")");
    } else if ((tmp=s.getEntryGuard())!=null) {
      out.printf("while(");
      nextExpr();
      tmp.accept(this);
      out.printf(")");      
    } else {
      out.printf("do");
    }
    if (s.get_before()!=null){
      out.printf("/*@ ");
      out.printf("with ");
      s.get_before().accept(this);
      out.printf(" */");
    }
    if (s.get_after()!=null){
      out.printf("/*@ ");
      out.printf("then ");
      s.get_after().accept(this);
      out.printf(" */");
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
  
  public void visit(MethodInvokation s){
    super.visit(s);
    if (s.get_before()!=null){
      out.printf("/*@ ");
      out.printf("with ");
      s.get_before().accept(this);
      out.printf(" */");
    }
    if (s.get_after()!=null){
      out.printf("/*@ ");
      out.printf("then ");
      s.get_after().accept(this);
      out.printf(" */");
    }    
  }
  public static TrackingTree dump_expr(PrintStream out,ASTNode node){
    TrackingOutput track_out=new TrackingOutput(out,false);
    JavaPrinter printer=new JavaPrinter(track_out);
    printer.setExpr();
    node.accept(printer);
    return track_out.close();
  }

  public static TrackingTree dump(PrintStream out,ProgramUnit program){
    hre.System.Debug("Dumping Java code...");
    try {
      TrackingOutput track_out=new TrackingOutput(out,false);
      JavaPrinter printer=new JavaPrinter(track_out);
      for(ASTClass cl:program.classes()){
        cl.accept(printer);
      }
      return track_out.close();
    } catch (Exception e) {
      System.out.println("error: ");
      e.printStackTrace();
      throw new Error("abort");
    }
  }

  public static void dump(PrintStream out, ASTNode cl) {
    TrackingOutput track_out=new TrackingOutput(out,false);
    JavaPrinter printer=new JavaPrinter(track_out);
    cl.accept(printer);
    track_out.close();    
  }
  
  public void visit(Dereference e){
    e.object.accept(this);
    out.printf(".%s",e.field);
  }
  
  public void visit(PrimitiveType t){
    switch(t.sort){
      case Array:
        t.getArg(0).accept(this);
        switch(t.getArgCount()){
        case 1:
            out.printf("[]");
            return;
        case 2:
          out.printf("[/*");
          t.getArg(1).accept(this);
          out.printf("*/]");
          return;
        default:
            Fail("Array type constructor with %d arguments instead of 1 or 2",t.getArgCount());
        }
      case Cell:
        if (t.getArgCount()==2){
          out.printf("cell<");
          t.getArg(0).accept(this);
          out.printf(">[");
          t.getArg(1).accept(this);
          out.printf("]");
          break;
        }
        if (t.getArgCount()!=1){
          Fail("Cell type constructor with %d arguments instead of 1",t.getArgCount());
        }
        out.printf("cell<");
        t.getArg(0).accept(this);
        out.printf(">");
        break;
      case Sequence:
        if (t.getArgCount()!=1){
          Fail("Sequence type constructor with %d arguments instead of 1",t.getArgCount());
        }
        out.printf("seq<");
        t.getArg(0).accept(this);
        out.printf(">");
        break;
      default:
        super.visit(t);
    }
  }
  
  @Override
  public void visit(ParallelBlock pb){
    if(pb.contract==null){
      Warning("parallel block with null contract!");
    } else {
      visit(pb.contract);
    }
    out.printf("kernel(%s,",pb.decl.getName());
    nextExpr();
    pb.count.accept(this);
    out.printf(")");
    pb.block.accept(this);
  }

  @Override
  public void visit(ParallelBarrier pb){
    if(pb.contract==null){
      Fail("parallel barrier with null contract!");
    } else {
      out.println("barrier{");
      out.incrIndent();
      visit(pb.contract);
      out.decrIndent();
      out.println("}");
    }
  }
  
}

