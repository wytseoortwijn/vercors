package vct.col.ast

class BooleanValue(val value:Boolean) extends Value {
  def getValue() : Boolean = value
  override def toString() : String = if (value) "true" else "false"
  override def equals(o:Any) : Boolean = o.equals(value)
}