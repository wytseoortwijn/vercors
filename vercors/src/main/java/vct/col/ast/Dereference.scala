package vct.col.ast

import vct.col.util.VisitorHelper

class Dereference(val `object`:ASTNode, val field:String) extends ASTNode with VisitorHelper {
  override def accept_simple[T,A](map:ASTMapping1[T,A], arg:A) = map.map(this, arg)
  override def accept_simple[T](visitor:ASTVisitor[T]) = try visitor.visit(this) catch { case t:Throwable => handle_throwable(t) }
  override def accept_simple[T](map:ASTMapping[T]) = try map.map(this) catch { case t:Throwable => handle_throwable(t) }
  
  override def `match`(ast:ASTNode) = ast match {
    case h:Hole => h.`match`(this)
    case d:Dereference => if (field.equals(d.field)) `object`.`match`(d.`object`) else false
    case _ => false
  }
}
