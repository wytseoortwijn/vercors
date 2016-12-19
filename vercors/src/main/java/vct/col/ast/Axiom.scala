package vct.col.ast

import vct.col.util.VisitorHelper
import vct.util.ClassName

class Axiom(val _name:String, val rule:ASTNode) extends ASTDeclaration(_name) with VisitorHelper {
  def getName() = name
  def getRule() = rule
  
  override def accept_simple[T,A](map:ASTMapping1[T,A], arg:A) = map.map(this, arg)
  override def getDeclName() = new ClassName(name)
  
  override def accept_simple[T](visitor:ASTVisitor[T]) = {
    try visitor.visit(this)
    catch {
      case t:Throwable => handle_throwable(t)
    }
  }
  
  override def accept_simple[T](map:ASTMapping[T]) : T = {
    try return map.map(this)
    catch {
      case t:Throwable => handle_throwable(t)
    }
  }
}