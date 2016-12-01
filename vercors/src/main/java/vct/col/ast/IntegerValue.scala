package vct.col.ast

class IntegerValue(val value:Int) extends Value {
  def getValue() : Int = value
  override def toString() : String = Integer.toString(value)
  override def equals(o:Any) : Boolean = o.equals(value)
}