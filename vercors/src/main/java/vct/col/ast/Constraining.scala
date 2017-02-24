package vct.col.ast

import vct.col.util.VisitorHelper

case class Constraining(val block:BlockStatement, val vars:List[NameExpression]) extends ASTNode with VisitorHelper {
  def this(block:BlockStatement, vars:Array[NameExpression]) = this(block, vars.toList)
  
  /** Gives the number of variables in this constraining block */
  @deprecated("this method will be removed", "soon")
  def varsLength = vars.length
  
  /** Yields the `i`-th variable of this constraining block */
  @deprecated("this method will be removed", "soon")
  def getVar(i:Int) = vars(i)
  
  /** Gives a copy of the vars list for Java interoperability */
  @deprecated("this method will be removed", "soon")
  def varsArray = vars.toArray
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
}
