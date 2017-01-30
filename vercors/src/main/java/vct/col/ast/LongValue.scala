package vct.col.ast

case class LongValue(val value:Long) extends Value {
  override def equals(a:Any) = a.equals(value)
  override def toString() = value.toString()
}