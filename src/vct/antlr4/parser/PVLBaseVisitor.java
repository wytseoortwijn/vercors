package vct.antlr4.parser;

import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;

import pv.parser.PVFullParser.Fence_listContext;
import pv.parser.PVFullParser.*;

public class PVLBaseVisitor<T> implements PVFullExtendedVisitor<T>{

  @Override
  public T visitStatement(StatementContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitField(FieldContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitInvariant(InvariantContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitClaz(ClazContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitLexpr(LexprContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitContract(ContractContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitArgs(ArgsContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitProgram(ProgramContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitBlock(BlockContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitExpr(ExprContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitMethod(MethodContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitType(TypeContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitFunction(FunctionContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visit(ParseTree arg0) {
    hre.System.Fail("missing case in %s: %s%ncaused by parse tree %s",this.getClass(),arg0.getClass(),arg0.toStringTree());
    return null;
  }

  @Override
  public T visitChildren(RuleNode arg0) {
    visit(arg0);
    return null;
  }

  @Override
  public T visitErrorNode(ErrorNode arg0) {
    visit(arg0);
    return null;
  }

  @Override
  public T visitTerminal(TerminalNode arg0) {
    visit(arg0);
    return null;
  }

  @Override
  public void enter(ParseTree arg0) {
  }

  @Override
  public void leave(ParseTree arg0) {
  }

  protected PVLWrappingVisitor<T> main;
  
  public void setMain(PVLWrappingVisitor<T> main){
    this.main=main;
  }

  @Override
  public T visitTuple(TupleContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitKernel_field(Kernel_fieldContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitKernel(KernelContext ctx) {
    visit(ctx);
    return null;
  }

  @Override
  public T visitFence_list(Fence_listContext ctx) {
    visit(ctx);
    return null;
  }
  

}
