package vct.col.ast

import vct.col.util.VisitorHelper

class TypeExpression(val op:TypeOperator, val types:Array[Type]) extends Type with VisitorHelper {
  def this(op:TypeOperator, types:Type*) = this(op, types.toArray)
  
  def firstType() = types.head
  def getTypes() = types
  def getType(i:Int) = types.apply(i)
  def getOp() = op
  def nrOfTypes() = types.length
  
  override def isNumeric() = {
    op match {
      case TypeOperator.Local | TypeOperator.Global | TypeOperator.Long => types.head.isNumeric()
      case _ => false
    }
  }
  
  override def supertypeof(context:ProgramUnit, t:Type) = false
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
  
  override def accept_simple[T](map:TypeMapping[T]) : T = {
    try return map.map(this)
    catch {
      case t:Throwable => handle_throwable(t)
    }
  }
}
