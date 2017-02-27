package vct.col.ast

import vct.col.util.VisitorHelper

case class ParallelBlock (val label:String, val contract:Contract, val iters:List[DeclarationStatement], val block:BlockStatement, val deps:Array[ASTNode]) extends ASTNode with VisitorHelper {
  require(deps != null, "dependency array is null")
  require(iters != null, "iteration list is null")
  
  /** Constructs a new parallel block from an array (`iters`) of iteration statements */
  def this(label:String, contract:Contract, iters:Array[DeclarationStatement], block:BlockStatement, deps:Array[ASTNode]) = this(label, contract, iters.toList, block, deps)
  
  /** Gives a copy of the iteration list for Java interoperability */
  @deprecated("this method will be removed", "soon")
  def itersArray = iters.toArray
  
  /** Yields the number of iteration statements */
  @deprecated("this method will be removed", "soon")
  def itersLength = iters.length
  
  /** Gives the `i`-th iteration statement */
  @deprecated("this method will be removed", "soon")
  def iteration(i:Int) = iters(i)
  
  /** Yields the number of dependencies */
  def depsLength = deps.length

  /** Gives the `i`-th dependency */
  def dependency(i:Int) = deps(i)
  
  /** Assigns `value` to the `i`-th dependency */
  def dependency(i:Int, value:ASTNode) = deps(i) = value
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
}
