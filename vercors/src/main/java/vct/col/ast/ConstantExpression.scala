package vct.col.ast

import hre.ast.Origin
import vct.col.ast.PrimitiveType.Sort

/**
 * AST node for wrapping constant values, e.g. integers, booleans, strings, doubles, and longs.
 * 
 * @author sccblom, whmoortwijn
 * @param value The constant value that is wrapped by this node.
 */
class ConstantExpression(val value:Value) extends ASTNode {
  
  def this(v:Value, t:Type) = {
    this(v)
    setType(t)
  }
  
  def this(v:Value, t:Type, origin:Origin) = {
    this(v, t)
    setOrigin(origin)
  }
  
  def this(i:Int) = this(new IntegerValue(i), new PrimitiveType(Sort.Integer))
  def this(b:Boolean) = this(new BooleanValue(b), new PrimitiveType(Sort.Boolean))
  def this(s:String) = this(new StringValue(s), new PrimitiveType(Sort.String))
  def this(l:Long) = this(new LongValue(l), new PrimitiveType(Sort.Long))
	def this(d:Double) = this(new DoubleValue(d), new PrimitiveType(Sort.Double))
  
  def this(i:Int, origin:Origin) = {
    this(i)
    setOrigin(origin)
  }
	 
  def this(b:Boolean, origin:Origin) = {
    this(b)
    setOrigin(origin)
  }
    
  def this(s:String, origin:Origin) = {
    this(s)
    setOrigin(origin)
  }
  
  def this(l:Long, origin:Origin) = {
    this(l)
    setOrigin(origin)
  }

  def this(d:Double, origin:Origin) = {
    this(d)
    setOrigin(origin)
  }
  
  def getValue() : Value = value
  override def equals(o:Any) : Boolean = value.equals(o)
  override def isConstant(o:Any) : Boolean = equals(o)
  override def toString() : String = value.toString()
  
  private def handle_throwable(t:Throwable) = {
    if (ASTNode.thrown.get() != t) {
      System.err.printf("Triggered by %s:%n", getOrigin())
      ASTNode.thrown.set(t)
    }
		throw t
  }
    
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
  
  override def accept_simple[T,A](map:ASTMapping1[T,A], arg:A) : T = {
    return map.map(this, arg)
  }
  
  override def `match`(ast:ASTNode) : Boolean = {
    ast match {
      case h:Hole => h.`match`(this)
      case _ => ast.equals(value)
    }
  }
}
