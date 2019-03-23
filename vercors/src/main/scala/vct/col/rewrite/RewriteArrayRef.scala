package vct.col.rewrite

import hre.ast.MessageOrigin
import vct.col.ast._

import scala.collection.mutable

object RewriteArrayRef {
  val constructorName: mutable.Map[(Type, Int), String] = mutable.Map()
  val valuesName: mutable.Map[Type, String] = mutable.Map()

  val namesUsed: mutable.Set[String] = mutable.Set()

  def getUniqueName(str: String): String = {
    var result = str.replaceAll("[^a-zA-Z0-9$_']", "_")
    while(namesUsed contains str) {
      result += "$"
    }
    namesUsed += str
    str
  }

  def getArrayConstructor(t: Type, definedDimensions: Int): String = {
    constructorName getOrElseUpdate((t, definedDimensions), getUniqueName("new_" + t.toString))
  }

  def getArrayValues(t: Type): String = {
    valuesName getOrElseUpdate(t, getUniqueName("values_" + t.toString()))
  }
}

class RewriteArrayRef(source: ProgramUnit) extends AbstractRewriter(source) {
  override def rewriteAll(): ProgramUnit = {
    val res = super.rewriteAll()

    create.enter()
    create.setOrigin(new MessageOrigin("Array Constructors"))
    for (((t, definedDimensions), name) <- RewriteArrayRef.constructorName) {
      res.add(arrayConstructorFor(t, definedDimensions, name))
    }
    create.leave()

    create.enter()
    create.setOrigin(new MessageOrigin("Array Values Functions"))
    for ((t, name) <- RewriteArrayRef.valuesName) {
      res.add(arrayValuesFor(t, name))
    }
    create.leave()

    res
  }

  override def visit(operator: OperatorExpression): Unit = {
    operator.operator match {
      case StandardOperator.NewArray =>
        result = create.invokation(
          null, null,
          RewriteArrayRef.getArrayConstructor(operator.arg(0).asInstanceOf[Type], operator.args.length - 1),
          operator.args.tail:_*)
      case StandardOperator.Subscript =>
        var baseType: Type = operator.arg(0).getType()
        var result = rewrite(operator.arg(0))
        val subscript = rewrite(operator.arg(1))

        if(baseType.isPrimitive(PrimitiveSort.Option)) {
          result = create.expression(StandardOperator.OptionGet, result)
          baseType = baseType.asInstanceOf[PrimitiveType].firstarg.asInstanceOf[Type]
        }

        if(!(baseType.isPrimitive(PrimitiveSort.Array) || baseType.isPrimitive(PrimitiveSort.Sequence))) {
          Fail("Unsupported array format")
        } else {
          result = create.expression(StandardOperator.Subscript, result, subscript)
          baseType = baseType.asInstanceOf[PrimitiveType].firstarg.asInstanceOf[Type]
        }

        if(baseType.isPrimitive(PrimitiveSort.Cell)) {
          result = create.dereference(result, "item")
          baseType = baseType.asInstanceOf[PrimitiveType].firstarg.asInstanceOf[Type]
        }

        this.result = result
      case _ =>
        super.visit(operator)
    }
  }

  override def visit(struct_value: StructValue): Unit = {
    RewriteArrayRef.getArrayConstructor(struct_value.getType, 1)
    super.visit(struct_value)
  }

  def quantify(dimension: Int, claim: ASTNode): ASTNode = {
    if(dimension == 0) {
      claim
    } else {
      val declarations = for(i <- 0 until dimension) yield new DeclarationStatement("i" + i, create.primitive_type(PrimitiveSort.Integer))
      val guards = for(i <- 0 until dimension) yield and(lte(constant(0), name("i"+i)), less(name("i"+i), name("size"+i)))
      create.starall(guards.reduce(and _), claim, declarations:_*)
    }
  }

  def arrayConstructorContract(contract: ContractBuilder, t: Type, value: ASTNode, dimension: Int, definedDimensions: Int): (Type, ASTNode) = {
    if(!t.isInstanceOf[PrimitiveType]) {
      return (t, value)
    }

    val pType = t.asInstanceOf[PrimitiveType]

    val claim = pType.sort match {
      case PrimitiveSort.Option => neq(value, create.reserved_name(ASTReserved.OptionNone))
      case PrimitiveSort.Array => eq(create.expression(StandardOperator.Length, value), name("size" + dimension))
      case PrimitiveSort.Cell => create.expression(StandardOperator.Perm, create.dereference(value, "item"), create.reserved_name(ASTReserved.FullPerm))
      case _ =>
        return (t, value)
    }

    contract.ensures(quantify(dimension, claim))

    val newType = pType.args.head.asInstanceOf[Type]

    val newValue = pType.sort match {
      case PrimitiveSort.Option => create.expression(StandardOperator.OptionGet, value)
      case PrimitiveSort.Array => create.expression(StandardOperator.Subscript, value, name("i" + dimension))
      case PrimitiveSort.Cell => create.dereference(value, "item")
    }

    val newDimension = if(pType.sort == PrimitiveSort.Array) dimension + 1 else dimension

    // If the last array dimension is accessed, only permit Cell types.
    if(newDimension == definedDimensions && !newType.isPrimitive(PrimitiveSort.Cell)) {
      return (newType, newValue)
    }

    arrayConstructorContract(contract, newType, newValue, newDimension, definedDimensions)
  }

  def arrayConstructorFor(t: Type, definedDimensions: Int, methodName: String): ASTNode = {
    val contract = new ContractBuilder()
    val result = create.reserved_name(ASTReserved.Result)
    val (elementType, elementValue) = arrayConstructorContract(contract, t, result, 0, definedDimensions)
    contract.ensures(quantify(definedDimensions, eq(elementValue, elementType.zero)))

    val methodArguments = for(i <- 0 until definedDimensions) yield new DeclarationStatement("size" + i, create.primitive_type(PrimitiveSort.Integer))

    val declaration = create.method_decl(t, contract.getContract, methodName, methodArguments.toArray, null)
    declaration.setStatic(true)
    declaration
  }

  def arrayValuesFor(t: Type, methodName: String): ASTNode = {
    null
  }
}