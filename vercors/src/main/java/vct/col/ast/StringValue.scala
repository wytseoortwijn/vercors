package vct.col.ast

class StringValue(val value:String) extends Value {
  def getValue() = value
  def getStripped() = value.substring(1, value.length() - 1)
  override def equals(o:Any) = o.equals(value)
  override def toString() = getValue()
}