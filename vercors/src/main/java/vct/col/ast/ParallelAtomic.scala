package vct.col.ast

import vct.col.util.VisitorHelper

case class ParallelAtomic (val block:BlockStatement, val synclist:List[ASTNode]) extends ASTNode with VisitorHelper {
  def this(block:BlockStatement, synclist:Array[ASTNode]) = this(block, synclist.toList)
  
  /** Yields a copy (as an array) of the sync list (for Java interoperability) */
  def synclistAsArray = synclist.toArray
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
}
