package vct.col.ast

import hre.ast.MessageOrigin

case class AssignmentStatement(val location:ASTNode, val expression:ASTNode) extends ASTNode {
  
  def this(name:String, expression:ASTNode) = {
    this(new NameExpression(name), expression)
    location.setOrigin(new MessageOrigin("parser bug: string location in assignment"))
  }
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = v.visit(this)
  override def accept_simple[T](m:ASTMapping[T]) = m.map(this)
}
