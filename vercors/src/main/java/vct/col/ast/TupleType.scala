package vct.col.ast

import vct.col.util.VisitorHelper

/**
 * AST node that represents `n`-tuple types, where the type
 * is of the form "`(T_1 * ... * T_n)`", represented by a list of `n` types.
 * 
 * @param types The (immutable) list of types that constitutes the tuple type.
 */
case class TupleType(val types:List[Type]) extends Type with VisitorHelper {
  def this(types:Array[Type]) = this(types.toList)
  
  /** @return A (copy of) the `types` list converted to an array (e.g for Java interoperability). */
  def typesToArray : Array[Type] = types.toArray

  /** @return The type "`T_i`" of the `i`-th tuple element. */
  def getType(i:Int) : Type = types.apply(i)
  
  /** @return The number of types represented by this AST node. */
  def nrOfTypes : Int = types.size

  /** @return Always `false`: no type can extend (inherit from) a tuple type. */
  override def supertypeof(context:ProgramUnit, t:Type) = false
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  override def accept_simple[T](m:TypeMapping[T]) = handle_standard(() => m.map(this))
}
