package vct.col.ast

class IntegerValue(val value:Int) extends Value {
  def getValue() = value
  override def toString() = Integer.toString(value)
  override def equals(o:Any) = o.equals(value)
}