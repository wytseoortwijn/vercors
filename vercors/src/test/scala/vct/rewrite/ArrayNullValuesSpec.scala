package vct.rewrite

import vct.col.ast._
import vct.col.rewrite.ArrayNullValues

class ArrayNullValuesSpec extends RewriteSpec(new ArrayNullValues(null)) {
  var ARRAY_TYPE = create.primitive_type(PrimitiveSort.Option, create.primitive_type(PrimitiveSort.Array, create.primitive_type(PrimitiveSort.Integer)))

  def

  "The ArrayNullValues pass" should "rewrite null values to none" in {
    var Null = create reserved_name ASTReserved.Null
    var none = create reserved_name ASTReserved.OptionNone

    Null asType ARRAY_TYPE should rewriteTo(none)


    it should "rewrite array comparison with null to none" in {

    }
  }
}
