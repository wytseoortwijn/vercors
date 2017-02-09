package vct.ast

import org.scalatest._
import scala.collection.mutable.ArrayBuffer
import scala.collection.JavaConverters._
import vct.col.ast._

class TupleTypeSpec extends FlatSpec with Matchers {
  
  "A Tuple Type" should "yield the correct type when queried for one" in {
    var inttype = new PrimitiveType(PrimitiveType.Sort.Integer)
    var booltype = new PrimitiveType(PrimitiveType.Sort.Boolean)
    var tupletype = new TupleType(Array[Type](inttype, booltype))
    
    tupletype.getType(0) should be (inttype)
    tupletype.getType(1) should be (booltype)
  }
  
  it should "throw out-of-bounds when accessing a non-existing type" in {
    var inttype = new PrimitiveType(PrimitiveType.Sort.Integer)
    var tupletype = new TupleType(Array[Type](inttype))
    
    a [IndexOutOfBoundsException] should be thrownBy {
      tupletype.getType(1) should be (inttype)
    }
  }

  it should "be immune to additions to the types array given to the constructor" in {
    var types = new ArrayBuffer[Type]()
    var inttype = new PrimitiveType(PrimitiveType.Sort.Integer)
    var booltype = new PrimitiveType(PrimitiveType.Sort.Boolean)
    
    types += inttype
    var tupletype = new TupleType(types.toArray)
    types += booltype
    
    a [IndexOutOfBoundsException] should be thrownBy {
      tupletype.getType(1) should be (booltype)
    }
  }
  
  it should "be immune to updates to the types array given to the constructor" in {
    var types = new ArrayBuffer[Type]()
    var inttype = new PrimitiveType(PrimitiveType.Sort.Integer)
    var booltype = new PrimitiveType(PrimitiveType.Sort.Boolean)
    
    types += inttype
    var tupletype = new TupleType(types.toArray)
    types(0) = booltype
    
    tupletype.getType(0) should be (inttype)
  }
  
  it should "also be immune to type updates from a Java array (after conversion)" in {
    var types = new java.util.ArrayList[Type]()
    var inttype = new PrimitiveType(PrimitiveType.Sort.Integer)
    var booltype = new PrimitiveType(PrimitiveType.Sort.Boolean)

    types.add(inttype)
    var tupletype = new TupleType(types.asScala.toArray)
    types.add(booltype)
    
    a [IndexOutOfBoundsException] should be thrownBy {
      tupletype.getType(1) should be (booltype)
    }
  }
  
  it should "(always) yield false when queried for a subtype" in {
    var inttype = new PrimitiveType(PrimitiveType.Sort.Integer)
    var tupletype = new TupleType(Array[Type](inttype))
    tupletype.supertypeof(null, inttype) should be (false)
  }
  
  it should "be able to accept no (or empty) type arguments" in {
    var tupletype = new TupleType(Array[Type]())
    tupletype.types.size should be (0)
  }
  
  it should "yield a type list of equal size as the one provided when queried for it" in {
    var inttype = new PrimitiveType(PrimitiveType.Sort.Integer)
    var booltype = new PrimitiveType(PrimitiveType.Sort.Boolean)
    var tupletype = new TupleType(Array[Type](inttype, booltype))
    
    tupletype.types.size should be (2)
  }
  
  it should "make the types getter immune for type updates" in {
    var types = new ArrayBuffer[Type]()
    var inttype = new PrimitiveType(PrimitiveType.Sort.Integer)
    var booltype = new PrimitiveType(PrimitiveType.Sort.Boolean)

    types += inttype
    var tupletype = new TupleType(types.toArray)
    types += booltype
    
    tupletype.types.size should be (1)
  }
  
  it should "prevent that updates to the internal types arrays reflect to the array given to the constructor" in {
    var types = new ArrayBuffer[Type]()
    var inttype = new PrimitiveType(PrimitiveType.Sort.Integer)
    var booltype = new PrimitiveType(PrimitiveType.Sort.Boolean)

    types += inttype
    var tupletype = new TupleType(types.toArray)
    tupletype.typesToArray.update(0, booltype)
    
    types(0) should be (inttype)
  }
}