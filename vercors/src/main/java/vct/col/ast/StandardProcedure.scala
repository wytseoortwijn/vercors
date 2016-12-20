package vct.col.ast

import vct.col.util.VisitorHelper

/**
  Simple class that wraps a StandardOperator as an ASTNode.
  Included in the design to support a future extension into functional languages:
  
  OperatorExpression(op,args) == ApplyExpression(StandardProcedure(op),args)
 */
class StandardProcedure(val operator:StandardOperator) extends ASTNode with VisitorHelper {
  override def accept_simple[T,A](map:ASTMapping1[T,A], arg:A) = map.map(this, arg)
  override def accept_simple[T](visitor:ASTVisitor[T]) = try visitor.visit(this) catch { case t:Throwable => handle_throwable(t) }
  override def accept_simple[T](map:ASTMapping[T]) = try map.map(this) catch { case t:Throwable => handle_throwable(t) }
}