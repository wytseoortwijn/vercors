package vct.col.ast

import vct.col.util.VisitorHelper
import vct.util.ClassName

class DeclarationStatement(val n:String, val t:Type, val expr:ASTNode) extends ASTDeclaration(n) with VisitorHelper {
  def this(name:String, t:Type) = this(name, t, null)
  
  override def getType() = t
  def getInit() = expr
  def getName() = n

  override def getDeclName() = {
    hre.lang.System.Debug("%s.%s", package_name, name)
    new ClassName(package_name, name);
  }
  
  override def accept_simple[T,A](map:ASTMapping1[T,A], arg:A) = map.map(this, arg)
    
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