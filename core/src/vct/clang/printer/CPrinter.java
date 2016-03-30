package vct.clang.printer;

import java.io.PrintStream;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTDeclaration;
import vct.col.ast.ASTNode;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.BlockStatement;
import vct.col.ast.Contract;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.IfStatement;
import vct.col.ast.Method;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.ProgramUnit;
import vct.col.ast.ReturnStatement;
import vct.util.AbstractPrinter;
import hre.ast.TrackingOutput;
import hre.ast.TrackingTree;

public class CPrinter extends AbstractPrinter {

	public CPrinter(TrackingOutput out) {
		super(CSyntax.getCML(), out);
	}

	public void pre_visit(ASTNode node) {
		super.pre_visit(node);
		for (NameExpression lbl : node.getLabels()) {
			nextExpr();
			lbl.accept(this);
			out.printf(":");
			// out.printf("[");
		}
	}
	
	public void post_visit(ASTNode node) {
	  super.post_visit(node);
	}

	public void visit(ASTClass cl){
		//if (cl.getDynamicCount()>0) {
		//	Fail("dynamic entries are illegal in C");
		//}
    for(ASTNode item:cl.dynamicMembers()){
      item.accept(this);
    }
    for(ASTNode item:cl.staticMembers()){
      item.accept(this);
    }
	}
	
	public void visit(DeclarationStatement decl){
		decl.getType().accept(this);
		out.printf(" %s",decl.getName());
		if (decl.getInit()!=null){
			out.printf("=");
			decl.getInit().accept(this);
		}
		if (!in_expr) {
			out.printf(";%n%n");
		}
	}
	
	@Override
	public void visit(Contract c){
	  out.println("/*@");
	  out.incrIndent();
    out.print("requires ");
    c.pre_condition.accept(this);
    out.println(";");
    out.print("ensures ");
    c.post_condition.accept(this);
    out.println(";");
	  out.decrIndent();
	  out.println("@*/");
	}
	public void visit(Method m){
	  Contract c=m.getContract();
	  if (c!=null) visit(c); //c.accept(this);
		nextExpr();
		m.getReturnType().accept(this);
		out.printf(" %s(",m.getName());
		String sep="";
		for(DeclarationStatement decl:m.getArgs()){
			out.printf("%s",sep);
			sep=",";
			nextExpr();
			decl.accept(this);
		}
		out.printf(")");
		if (m.getBody()!=null){
			m.getBody().accept(this);
			out.printf("%n%n");
		} else {
			out.printf(";%n%n");
		}
		
	}
	  public void visit(IfStatement s){
		      int N=s.getCount();
		      out.printf("if (");
		      nextExpr();
		      s.getGuard(0).accept(this);
		      out.printf(") ");
		      s.getStatement(0).accept(this);
		      for(int i=1;i<N;i++){
		        if (i==N-1 && s.getGuard(i)==IfStatement.else_guard){
		          out.printf(" else ");
		        } else {
		          out.printf(" else if (");
		          nextExpr();
		          s.getGuard(i).accept(this);
		          out.printf(")");
		        }
		        s.getStatement(i).accept(this);
		      }
		      out.lnprintf("");
		    }

	public void visit(AssignmentStatement s){
		nextExpr();
		s.getLocation().accept(this);
		out.printf("=");
		nextExpr();
		s.getExpression().accept(this);
		if (in_expr){
			out.printf(";%n");
		}
	}
	public void visit(ReturnStatement s){
		if (s.getExpression()==null){
			out.printf("return");
		} else {
			out.printf("return ");
			nextExpr();
			s.getExpression().accept(this);
		}
		if (in_expr){
			out.printf(";");
		} else {
			out.lnprintf(";");
		}
		
	}
	public void visit(BlockStatement block) {
		boolean block_expr=in_expr;
		if (block_expr) {
			out.printf("{");
		} else {
			out.lnprintf("{");
			out.incrIndent();
		}
		int N=block.getLength();
		for(int i=0;i<N;i++){
		  ASTNode S=block.getStatement(i);
		  S.accept(this);
			if (S instanceof OperatorExpression){
			  if (block_expr) out.printf(";"); else out.lnprintf(";");
			}
		}
		if (!block_expr) {
			out.decrIndent();
		}
		out.printf("}");
	}

	public static TrackingTree dump_expr(PrintStream out, ASTNode node) {
		TrackingOutput track_out = new TrackingOutput(out, false);
		CPrinter printer = new CPrinter(track_out);
		printer.setExpr();
		node.accept(printer);
		return track_out.close();
	}

	public static TrackingTree dump(PrintStream out, ProgramUnit program) {
		hre.System.Debug("Dumping C code...");
		try {
			TrackingOutput track_out = new TrackingOutput(out, false);
			CPrinter printer = new CPrinter(track_out);
			for (ASTDeclaration cu: program.get()) {
				cu.accept(printer);
			}
			return track_out.close();
		} catch (Exception e) {
			System.out.println("error: ");
			e.printStackTrace();
			throw new Error("abort");
		}
	}

	public static void dump(PrintStream out, ASTNode cl) {
		TrackingOutput track_out = new TrackingOutput(out, false);
		CPrinter printer = new CPrinter(track_out);
		cl.accept(printer);
		track_out.close();
	}

}
