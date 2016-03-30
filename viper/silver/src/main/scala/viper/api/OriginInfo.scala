package viper.api

import viper.silver.ast.Info

class OriginInfo[O](origin : O) extends Info {
  val loc=origin
  override def comment: Seq[String] = Nil
  
  override def toString():String = loc.toString()
}
