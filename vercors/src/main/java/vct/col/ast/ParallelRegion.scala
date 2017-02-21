package vct.col.ast

import vct.col.util.VisitorHelper

case class ParallelRegion (val contract:Contract, val blocks:List[ParallelBlock]) extends ASTNode with VisitorHelper {
  def this(contract:Contract, blocks:Array[ParallelBlock]) = this(contract, blocks.toList)
  
  /** Gives a copy of the blocks list (as an `Array`) for Java interoperability */
  def blocksArray = blocks.toArray
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
}
