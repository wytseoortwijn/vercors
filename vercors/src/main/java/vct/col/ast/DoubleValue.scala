package vct.col.ast

/** Represents a constant double with value "`value`". */
case class DoubleValue(val value:Double) extends Value {
  override def equals(a:Any) = a.equals(value)
  override def toString() = value.toString()
}
