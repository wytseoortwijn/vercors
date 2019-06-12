package vct.col.rewrite

import vct.col.ast.stmt.decl.{DeclarationStatement, Method, ProgramUnit}
import hre.lang.System.{Abort, Debug, DebugException, Fail, Output, Warning, Failure}
import vct.col.ast.`type`.PrimitiveSort
import vct.col.ast.expr.{MethodInvokation, NameExpression, OperatorExpression, StandardOperator}
import vct.col.ast.generic.ASTNode
import vct.col.util.SequenceUtils

import scala.collection.JavaConversions._
import scala.collection.mutable.ListBuffer

class LiftDeclarations(arg: ProgramUnit) extends AbstractRewriter(arg) {
  override def visit(decl: DeclarationStatement): Unit = {
    Debug("%s %s", decl.`type`, decl.name)
    val newType = SequenceUtils.optArrayCell(create, decl.`type`)
    val newStructType = SequenceUtils.arrayCell(create, decl.`type`)

    result = DeclarationStatement(
      decl.name,
      newType,
      Some(create.expression(StandardOperator.OptionSome, create.struct_value(newStructType, null, decl.`type`.zero)))
    )
    result.setOrigin(decl.getOrigin)
  }

  override def visit(invokation: MethodInvokation): Unit = {
    result = create.invokation(
      copy_rw.rewrite(invokation.`object`),
      rewrite(invokation.dispatch),
      invokation.method,
      rewrite(invokation.getArgs):_*
    )
  }

  override def visit(method: Method): Unit = {
    var body: ListBuffer[ASTNode] = ListBuffer()
    var args: ListBuffer[DeclarationStatement] = ListBuffer()

    for(arg <- method.getArgs) {
      args += create.field_decl(arg.getOrigin, "__arg_" + arg.name, arg.`type`)
      body += create.field_decl(arg.getOrigin, arg.name, SequenceUtils.optArrayCell(create, arg.`type`))
      body += create.assignment(SequenceUtils.access(create, create.unresolved_name(arg.name), create.constant(0)), create.unresolved_name("__arg_" + arg.name))
    }

    body += rewrite(method.getBody)

    result = create.method_decl(
      method.getReturnType,
      rewrite(method.getContract),
      method.getName,
      args,
      create.block(body:_*)
    )
  }

  override def visit(name: NameExpression): Unit = {
    result = SequenceUtils.access(create, create.unresolved_name(name.getName), create.constant(0))
  }
}
