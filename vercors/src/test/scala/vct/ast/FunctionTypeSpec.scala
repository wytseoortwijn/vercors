package vct.ast

import hre.lang.HREExitException
import org.scalatest._
import vct.col.ast._

class FunctionTypeSpec extends FlatSpec with Matchers  {
  
  "A function type" should "be constructable normally" in {
    var param1 = new ClassType(Array("Int"))
    var param2 = new ClassType(Array("Bool"))
    var result = new ClassType(Array("Bool"))
    var ft = new FunctionType(Array[Type](param1, param2), result)
    ft.getArity should be (2)
    
  }
  
  it should "be constructable with arity 0" in {
    var result = new ClassType(Array("Bool"))
    var ft = new FunctionType(Array[Type](), result)
    ft.getArity should be (0)
  }
  
  it should "not be constructable when the parameter list is null" in {
    var params : java.util.ArrayList[Type] = null
    var result = new ClassType(Array("Bool"))
    a [HREExitException] should be thrownBy {
      var ft = new FunctionType(params, result)
    }
  }
  
  it should "not be constructable when the return type is null" in {
    var param1 = new ClassType(Array("Int"))
    var param2 = new ClassType(Array("Bool"))
    a [HREExitException] should be thrownBy {
      var ft = new FunctionType(Array[Type](param1, param2), null)
    }
  }
  
  it should "yield the correct parameter when queried for" in {
    var param1 = new ClassType(Array("Int"))
    var param2 = new ClassType(Array("Bool"))
    var result = new ClassType(Array("Bool"))
    var ft = new FunctionType(Array[Type](param1, param2), result)
    ft.getArgument(0) should be (param1)
    ft.getArgument(1) should be (param2)
    ft.getResult should be (result)
  }
  
  it should "yield null as its zero element" in {
    var param = new ClassType(Array("Int"))
    var result = new ClassType(Array("Bool"))
    var ft = new FunctionType(Array[Type](param), result)
    ft.zero() should be (null)
  }
  
  it should "not be a supertype of any other type" in {
    var param = new ClassType(Array("Int"))
    var result = new ClassType(Array("Bool"))
    var ft = new FunctionType(Array[Type](param), result)
    var anyType = new ClassType(Array("Anything"))
    ft.supertypeof(null, anyType) should be (false)
  }
  
  it should "not be equal to null" in {
    var param = new ClassType(Array("Int"))
    var result = new ClassType(Array("Bool"))
    var ft = new FunctionType(Array[Type](param), result)
    ft.equals(null) should be (false)
  }
  
  it should "not be equal to anything that is not a function type" in {
    var param = new ClassType(Array("Int"))
    var result = new ClassType(Array("Bool"))
    var ft = new FunctionType(Array[Type](param), result)
    var anyType = new ClassType(Array("Anything"))
    ft.equals(anyType) should be (false)
  }
  
  it should "not be equal to a function type with a different signature" in {
    var param11 = new ClassType(Array("Int"))
    var param12 = new ClassType(Array("Bool"))
    var result1 = new ClassType(Array("Bool"))
    var ft1 = new FunctionType(Array[Type](param11, param12), result1)
    
    var param21 = new ClassType(Array("Bool"))
    var param22 = new ClassType(Array("Int"))
    var result2 = new ClassType(Array("Bool"))
    var ft2 = new FunctionType(Array[Type](param21, param22), result2)
    
    ft1.equals(ft2) should be (false)
  }
  
  it should "be equal to a function type constructed with the same signature" in {
    var param = new ClassType(Array("Int"))
    var result = new ClassType(Array("Bool"))
    var ft1 = new FunctionType(Array[Type](param), result)
    var ft2 = new FunctionType(Array[Type](param), result)
    ft1.equals(ft2) should be (true)
  }
  
  it should "be equal to a function type constructed with a similar signature" in {
    var param1 = new ClassType(Array("Int"))
    var param2 = new ClassType(Array("Int"))
    var result1 = new ClassType(Array("Bool"))
    var result2 = new ClassType(Array("Bool"))
    var ft1 = new FunctionType(Array[Type](param1), result1)
    var ft2 = new FunctionType(Array[Type](param2), result2)
    ft1.equals(ft2) should be (true)
  }
}