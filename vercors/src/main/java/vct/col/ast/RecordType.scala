package vct.col.ast

import vct.col.util.VisitorHelper

/** A single type entry of a record type (only used in `RecordType`). */
case class RecordTypeEntry(val recordName:String, val recordType:Type)

/**
 * AST node that represents record types, that is, pairs of variable names (identifiers)
 * and their types. 
 */
case class RecordType(val types:List[RecordTypeEntry]) extends Type with VisitorHelper {
  /** Instantiates a new record type from separate lists of `names` and `types`. */
  def this(names:List[String], types:List[Type]) = 
    this((names, types).zipped map (new RecordTypeEntry(_,_)))
  
  /** @return The number of fields in this record. */
  def fieldCount = types.length
  
  /** @return The name of the {@code i}-th record field. */
  def fieldName(i:Int) = types.apply(i).recordName
  
  /** @return The type of the {@code i}-th record field. */
  def fieldType(i:Int) = types.apply(i).recordType
  
  /** @return Always `false`: no type can extend (inherit from) a record type. */
  override def supertypeof(context:ProgramUnit, t:Type) = false
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  override def accept_simple[T](m:TypeMapping[T]) = handle_standard(() => m.map(this))
}
