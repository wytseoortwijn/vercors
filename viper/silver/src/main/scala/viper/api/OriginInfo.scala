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
  
  var gonogo : viper.api.VerificationControl[Object] = AlwaysGo;

}

object VControl {
  
  def get_origin[O](info : viper.silver.ast.Info):O ={
    if (info.isInstanceOf[OriginInfo[O]]){
      info.asInstanceOf[OriginInfo[O]].loc;
    } else {
      null.asInstanceOf[O];
    }
  }

  var time : Long=0;
  
  def gonogo(fun : viper.silver.ast.Function):Boolean={
    time=System.currentTimeMillis();
    val res=Reachable.gonogo.function(get_origin(fun.info),fun.name)
    System.err.printf("function %s: %s%n",fun.name,if (res) "Go" else "Skip");
    res
  }
  
  def report(fun : viper.silver.ast.Function,result : Boolean)={
    if (result) {
      Reachable.gonogo.pass(get_origin(fun.info));
    } else {
      Reachable.gonogo.fail(get_origin(fun.info));
    }
    System.err.printf("function %s: %s (%dms)%n",
        fun.name,
        (if (result) "Pass" else "Fail"),
        new java.lang.Long(System.currentTimeMillis()-time));
  }
  
  def gonogo(fun : viper.silver.ast.Predicate):Boolean={
    time=System.currentTimeMillis();
    val res=Reachable.gonogo.predicate(get_origin(fun.info),fun.name)
    System.err.printf("predicate %s: %s%n",fun.name,if (res) "Go" else "Skip");
    res
  }
  
  def report(fun : viper.silver.ast.Predicate,result : Boolean)={
    if (result) {
      Reachable.gonogo.pass(get_origin(fun.info));
    } else {
      Reachable.gonogo.fail(get_origin(fun.info));
    }
    System.err.printf("predicate %s: %s (%dms)%n",
        fun.name,
        (if (result) "Pass" else "Fail"),
        new java.lang.Long(System.currentTimeMillis()-time));
  }
  
  def gonogo(fun : viper.silver.ast.Method):Boolean={
    time=System.currentTimeMillis();
    val res=Reachable.gonogo.method(get_origin(fun.info),fun.name)
    System.err.printf("method %s: %s%n",fun.name,if (res) "Go" else "Skip");
    res
  }
  
  def report(fun : viper.silver.ast.Method,result : Boolean)={
    if (result) {
      Reachable.gonogo.pass(get_origin(fun.info));
    } else {
      Reachable.gonogo.fail(get_origin(fun.info));
    }
    System.err.printf("method %s: %s (%dms)%n",
        fun.name,
        (if (result) "Pass" else "Fail"),
        new java.lang.Long(System.currentTimeMillis()-time));
  }
  
}

object AlwaysGo extends viper.api.VerificationControl[Object] {
 def function(x$1: Object,x$2: String): Boolean = true
 def method(x$1: Object,x$2: String): Boolean = true
 def predicate(x$1: Object,x$2: String): Boolean = true
 def fail(x$1: Object): Unit = {}
 def pass(x$1: Object): Unit = {}
}
