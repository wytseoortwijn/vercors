package vct.mock

import vct.col.ast._

case class IntDeclarationMock(override val name:String, val value:Int) 
  extends DeclarationStatement(name, new PrimitiveType(PrimitiveSort.Integer), new ConstantExpression(new IntegerValue(value)))