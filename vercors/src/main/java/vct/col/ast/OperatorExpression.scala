package vct.col.ast

import hre.ast.FileOrigin
import scala.annotation.varargs
import vct.col.util.VisitorHelper

/**
 * Wytse: I used an extra static factory method here to retain the varargs functionality. Without the
 * "varargs" annotation the Java code breaks, and apparently constructors cannot have "varargs" annotations..
 */
object OperatorExpression {
  @varargs def construct(op:StandardOperator, args:ASTNode*) = new OperatorExpression(op, args:_*)
}

class OperatorExpression private[this] (val op:StandardOperator, val args:Array[ASTNode]) extends ExpressionNode with VisitorHelper {
  def getArguments() = args.clone()
  def getOperator() = op
  
  /** Use {@code OperatorExpression.construct(...)} to construct a new operator expression. */
  private def this(op:StandardOperator, args:ASTNode*) = {
    this(op, args.toArray)
    if (op.arity() >= 0 && args.length != op.arity()) {
      hre.lang.System.Abort("Wrong number of arguments for %s: got %d, but expected %d.", List(op, args.length, op.arity()))
    }
  }
  
  def getArg(i:Int) : ASTNode = {
    if (i >= args.length) 
      throw new Error(String.format("The operator %s does not have an argument %i.", List(op, i)))
    else args.apply(i)
  }
  
  def mergeOrigins() = {
    if (args.length < 2) 
      throw new Error("Cannot merge on less than 2 arguments.")
    if (!args.head.getOrigin.isInstanceOf[FileOrigin]) 
      throw new Error("The merge requires the left operator to have a FileOrigin.")
    if (!args.last.getOrigin.isInstanceOf[FileOrigin]) 
      throw new Error("The merge requires the right operator to have a FileOrigin.")
    
    var start = args.head.getOrigin.asInstanceOf[FileOrigin]
    var end = args.last.getOrigin.asInstanceOf[FileOrigin]
    setOrigin(start.merge(end))
  }
  
  override def isa(op:StandardOperator) = op == this.op
  override def accept_simple[T,A](map:ASTMapping1[T,A], arg:A) = map.map(this, arg)
  override def accept_simple[T](visitor:ASTVisitor[T]) = try visitor.visit(this) catch { case t:Throwable => handle_throwable(t) }
  override def accept_simple[T](map:ASTMapping[T]) = try map.map(this) catch { case t:Throwable => handle_throwable(t) }
  
  private[this] def match_compare(a:Array[ASTNode], b:Array[ASTNode]) : Boolean = {
    if (a.isEmpty || b.isEmpty) true
    if (a.head.`match`(b.head)) match_compare(a.tail, b.tail)
    else false
  }
  
  override def `match`(ast:ASTNode) = ast match {
    case h:Hole => h.`match`(this)
    case oe:OperatorExpression => if (oe.isa(op)) match_compare(args, oe.getArguments) else false
    case _ => false
  }
}
