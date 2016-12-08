package vct.col.ast

class LongValue(val value:Long) extends Value {
  def getValue() = value
  override def equals(a:Any) = a.equals(value)
  override def toString() = value.toString()
}