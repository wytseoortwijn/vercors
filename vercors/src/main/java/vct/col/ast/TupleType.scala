package vct.col.ast

import vct.col.util.VisitorHelper

/**
 * AST node that represents `n`-tuple types, where the type
 * is of the form "`(T_1 * ... * T_n)`", represented by a list of `n` types.
 * 
 * @param _types The list of types that constitutes the tuple type.
 */
class TupleType(private[this] val _types:Array[Type]) extends Type with VisitorHelper {
  /** The list of types that constitutes the type of the tuple. */
  val types = _types.toArray.clone()

  /** @return The type "`T_i`" of the `i`-th tuple element. */
  def `type`(i:Int) : Type = types.apply(i)

  /** @return Always `false`: no type can extend (inherit from) a tuple type. */
  override def supertypeof(context:ProgramUnit, t:Type) = false
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  override def accept_simple[T](m:TypeMapping[T]) = handle_standard(() => m.map(this))
}
