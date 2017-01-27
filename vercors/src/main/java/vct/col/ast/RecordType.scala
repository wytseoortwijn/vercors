package vct.col.ast

import vct.col.util.VisitorHelper

/**
 * AST node that represents record types, that is, pairs of variable names (identifiers)
 * and their types. This class assumes that {@code names.length} is equal to {@code types.length}
 * (this is however not enforced in the implementation). We also assume that the type {@code types[i]} 
 * corresponds to the identifier {@code names[i]}.
 * 
 * @param names The identifiers (field names) of the record type.
 * @param types The corresponding type names of the record fields.
 */
class RecordType(private[this] val names:Seq[String], private[this] val types:Seq[Type]) extends Type with VisitorHelper {
  /** Yields the number of fields in this record. */
  def fieldCount = names.length
  
  /** Yields the name of the {@code i}-th record field. */
  def fieldName(i:Int) = names.apply(i)
  
  /** Yields the type of the {@code i}-th record field. */
  def fieldType(i:Int) = types.apply(i)
  
  override def supertypeof(context:ProgramUnit, t:Type) = false
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  override def accept_simple[T](m:TypeMapping[T]) = handle_standard(() => m.map(this))
}
