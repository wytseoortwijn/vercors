package vct.col.ast

import vct.col.util.VisitorHelper

/**
 * AST node that represents the type of tuples, or actually {@code n}-tuples 
 * with types "{@code (T_1 * ... * T_n)}".
 * 
 * @param _types The list of types that constitutes the tuple type.
 */
class TupleType(private[this] val _types:Array[Type]) extends Type with VisitorHelper {
  /** The list of types that constitutes the type of the tuple. */
  val types = _types.clone()
  
  /** Yields the type "{@code T_i}" of the {@code i}-th element of tuples of "this" type. */
  def `type`(i:Int) = types.apply(i)

  override def supertypeof(context:ProgramUnit, t:Type) = false
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  override def accept_simple[T](m:TypeMapping[T]) = handle_standard(() => m.map(this))
}
