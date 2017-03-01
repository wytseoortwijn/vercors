package vct.col.ast

import hre.ast.FileOrigin
import scala.collection.JavaConverters._
import vct.col.util.VisitorHelper

case class OperatorExpression(val operator:StandardOperator, val args:List[ASTNode]) extends ExpressionNode with VisitorHelper {
  require(args != null, "The argument list is null")
  require(operator.arity < 0 || args.length == operator.arity, "Wrong number of arguments for $operator: got ${args.length}, but expected ${operator.arity}")
  
  /** Constructs a new operator expression from an array of arguments */
  def this(operator:StandardOperator, args:Array[ASTNode]) = this(operator, args.toList)
  
  /** Gives a Java wrapper (as a `java.util.List`) for the list of arguments. */
  def argsJava = args.asJava
  def first = args(0)
  def second = args(1)
  def third = args(2)
  
  /** Yields the number of arguments. Beware, `argslength` takes linear time, not constant time. */
  def argslength = args.length
  
  /** Either yields the `i`-th argument, or `None` if there is no such argument  */
  @deprecated("this method will be removed", "soon")
  def argOption(i:Int) = args.lift(i)
  
  /** Yields the `i`-th argument, or throws an exception if there is no such argument */
  @deprecated("this method will be removed", "soon")
  def arg(i:Int) = argOption(i) match {
    case None => throw new Error("the operator $operator does not have an argument $i.")
    case Some(argument) => argument
  }
  
  /** Merges the (file) origins of the leftmost and rightmost argument, provided there
   *  are at least two arguments. */
  def mergeOrigins() = {
    if (args.length < 2) throw new Error("cannot merge on less than 2 arguments.")
    else (args.head.getOrigin, args.last.getOrigin) match {
      case (left:FileOrigin, right:FileOrigin) => setOrigin(left merge right)
      case _ => throw new Error("merging requires both operands to have a FileOrigin.")
    }
  }
  
  override def `match`(ast:ASTNode) = ast match {
    case OperatorExpression(op, a) => (this isa op) && (args corresponds a)(_ `match` _)
    case h:Hole => h `match` this
    case _ => false
  }
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  override def isa(op:StandardOperator) = op == operator
}
