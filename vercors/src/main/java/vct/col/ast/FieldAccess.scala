package vct.col.ast

import vct.util.ClassName

class FieldAccess(val claz:ClassName, val obj:ASTNode, val name:String, val value:ASTNode) extends ASTNode {
  /** The fully qualified name of the class in which the variable is to be accessed. */
  def getClassName() = claz
  
  /** The object the be accessed or null for a static variable. */
  def getObject() = obj
  
  /** The name of the field to be accessed. */
  def getName() = name
  
  /** This field is non-null for a write and null for a read. */
  def getValue() = value
  
  override def accept_simple[T,A](map:ASTMapping1[T,A], arg:A) = map.map(this, arg)
  override def accept_simple[T](visitor:ASTVisitor[T]) = visitor.visit(this)
  override def accept_simple[T](map:ASTMapping[T]) = map.map(this)
}