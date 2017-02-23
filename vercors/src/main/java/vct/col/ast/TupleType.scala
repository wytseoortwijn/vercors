package vct.col.ast

import hre.lang.System.Abort
import vct.col.util.VisitorHelper

/**
 * AST node that represents `n`-tuple types, where the type
 * is of the form "`(T_1 * ... * T_n)`", represented by a list of `n` types.
 * 
 * @param types The (immutable) list of types that constitutes the tuple type.
 * @author sccblom, whmoortwijn
 */
case class TupleType(val types:List[Type]) extends Type with VisitorHelper {
  require(types != null, "The tuple types list is null.")
  require(!types.isEmpty, "Tuple types must have at least one type entry.")
  
  /** Instantiates a tuple type from an array of types. */
  def this(types:Array[Type]) = this(types.toList)
  
  /** Gives a (copy of) the `types` list converted to an array (e.g for Java interoperability). */
  def typesToArray = types.toArray

  /** Yields the type "`T_i`" of the `i`-th tuple element. */
  def getType(i:Int) = types.apply(i)
  
  /** Gives the number of types represented by this AST node. */
  def nrOfTypes = types.size

  /** @return Always `false`: no type can extend (inherit from) a tuple type. */
  override def supertypeof(context:ProgramUnit, t:Type) = false
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  override def accept_simple[T](m:TypeMapping[T]) = handle_standard(() => m.map(this))
}
