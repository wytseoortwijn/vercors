package vct.col.ast

import vct.col.util.VisitorHelper

case class Dereference(val obj:ASTNode, val field:String) extends ASTNode with VisitorHelper {
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  
  override def `match`(ast:ASTNode) = ast match {
    case Dereference(o, `field`) => o `match` obj
    case h:Hole => h `match` this
    case _ => false
  }
}
