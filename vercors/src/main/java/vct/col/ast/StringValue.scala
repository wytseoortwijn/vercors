package vct.col.ast

/** Represents a constant string with value "`value`". */
case class StringValue(val value:String) extends Value {
  override def equals(o:Any) = o.equals(value)
  override def toString = value
}
