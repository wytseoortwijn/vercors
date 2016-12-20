package vct.col.ast

import vct.util.ClassName

/**
 * @param classname The fully qualified name of the class in which the variable is to be accessed.
 * @param object The object the be accessed or null for a static variable.
 * @param name The name of the field to be accessed.
 * @param value This field is non-null for a write and null for a read.
 */
class FieldAccess(val classname:ClassName, val `object`:ASTNode, val name:String, val value:ASTNode) extends ASTNode {
  override def accept_simple[T,A](map:ASTMapping1[T,A], arg:A) = map.map(this, arg)
  override def accept_simple[T](visitor:ASTVisitor[T]) = visitor.visit(this)
  override def accept_simple[T](map:ASTMapping[T]) = map.map(this)
}