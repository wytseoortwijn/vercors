package vct.ast

import org.scalatest._
import scala.collection.JavaConverters._
import vct.col.ast._

class RecordTypeSpec extends FlatSpec with Matchers {
  
  "A Record Type" should "successfully instantiate after invoking the default constructor" in {
    var record = new RecordType(List(
      new RecordTypeEntry("field1", new PrimitiveType(PrimitiveType.Sort.Integer)),
      new RecordTypeEntry("field2", new PrimitiveType(PrimitiveType.Sort.Boolean))
    ))
    
    record.types.size should be (2)
    record.fieldName(0) should be ("field1")
    record.fieldName(1) should be ("field2")
  }
  
  it should "successfully instantiate after calling the alternative constructor (with expected input)" in {
    var names = List("field1", "field2")
    var types = List(new PrimitiveType(PrimitiveType.Sort.Integer), new PrimitiveType(PrimitiveType.Sort.Boolean))
    var record = new RecordType(names, types)
    
    record.types.size should be (2)
    record.fieldName(0) should be ("field1")
    record.fieldName(1) should be ("field2")
  }
  
  it should "successfully instantiate after providing too many names" in {
    var names = List("field1", "field2", "field3")
    var types = List(new PrimitiveType(PrimitiveType.Sort.Integer), new PrimitiveType(PrimitiveType.Sort.Boolean))
    var record = new RecordType(names, types)
    
    record.types.size should be (2)
    record.fieldName(0) should be ("field1")
    record.fieldName(1) should be ("field2")
  }
  
  it should "successfully instantiate after providing too many types" in {
    var names = List("field1", "field2")
    var types = List(
        new PrimitiveType(PrimitiveType.Sort.Integer), 
        new PrimitiveType(PrimitiveType.Sort.Boolean), 
        new PrimitiveType(PrimitiveType.Sort.Integer))
    var record = new RecordType(names, types)
    
    record.types.size should be (2)
  }
}