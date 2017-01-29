package vct.col.ast

/**
 * Represents a catch-clause for use in a try-catch-finally block, for example: 
 * "`catch (ExceptionType e) { S }`", with "`S`" the catch-clause body.
 * 
 * @param decl The declaration that determines the exception type to handle (e.g. "`ExceptionType e`").
 * @param block The body statement block of the catch clause (e.g. the handler body "`S`").
 */
case class CatchClause(val decl:DeclarationStatement, val block:BlockStatement)
