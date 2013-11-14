package vct.antlr4.parser;

import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;

import pv.parser.*;
import pv.parser.PVFullParser.Fence_listContext;
import pv.parser.PVFullParser.*;
import vct.col.ast.*;

public class PVLWrappingVisitor<E> implements PVFullVisitor<E>{

  private PVFullExtendedVisitor<E> nested;
  
  public PVLWrappingVisitor(PVFullExtendedVisitor<E> visitor) {
    nested=visitor;
    visitor.setMain(this);
  }

  @Override
  public E visit(ParseTree arg0) {
    nested.enter(arg0);
    E res=arg0.accept(nested);;
    nested.leave(arg0);
    return res;
  }

  @Override
  public E visitChildren(RuleNode arg0) {
    nested.enter(arg0);
    E res=arg0.accept(nested);
    nested.leave(arg0);
    return res;
  }

  @Override
  public E visitErrorNode(ErrorNode arg0) {
    nested.enter(arg0);
    E res=arg0.accept(nested);;
    nested.leave(arg0);
    return res;
  }

  @Override
  public E visitTerminal(TerminalNode arg0) {
    nested.enter(arg0);
    E res=arg0.accept(nested);;
    nested.leave(arg0);
    return res;
  }

  @Override
  public E visitStatement(StatementContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitField(FieldContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitInvariant(InvariantContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitClaz(ClazContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitLexpr(LexprContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitContract(ContractContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitArgs(ArgsContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitProgram(ProgramContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitBlock(BlockContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitExpr(ExprContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitMethod(MethodContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitType(TypeContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitFunction(FunctionContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitTuple(TupleContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitKernel_field(Kernel_fieldContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitKernel(KernelContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

  @Override
  public E visitFence_list(Fence_listContext ctx) {
    nested.enter(ctx);
    E res=ctx.accept(nested);;
    nested.leave(ctx);
    return res;
  }

}
