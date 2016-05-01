package viper.api

import viper.silver.ast.Info
import viper.silver.ast.Function

class OriginInfo[O](origin : O) extends Info {
  val loc=origin
  override def comment: Seq[String] = Nil
  
  override def toString():String = loc.toString()
}

class RefuteInfo[O](origin : O) extends OriginInfo[O](origin) {
  // This class is used to tag a Not that is the result of
  // encoding "refute x;" as "assert !x;". 
}

object Reachable {
  var reachable = scala.collection.mutable.Set[Info]()
  
  var gonogo : viper.api.VerficationControl = null;

}

