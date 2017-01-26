package vct.col.ast

import vct.col.util.VisitorHelper

class RecordType(private[this] val names:Seq[String], private[this] val types:Seq[Type]) extends Type with VisitorHelper {
  def fieldCount = names.length
  def fieldName(i:Int) = names.apply(i)
  def fieldType(i:Int) = types.apply(i)
  
  override def supertypeof(context:ProgramUnit, t:Type) = false
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  override def accept_simple[T](m:TypeMapping[T]) = handle_standard(() => m.map(this))
}
