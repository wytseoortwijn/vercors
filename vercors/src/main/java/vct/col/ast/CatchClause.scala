package vct.col.ast

/**
 * Represents a catch-clause for use in a try-catch-finally block, for example: 
 * "{@code catch (ExceptionType e) S}", with "{@code S}" the body of the catch-clause.
 * 
 * @param decl The declaration that determines the exception type to handle (e.g. "{@code ExceptionType e}").
 * @param block The body statement block of the catch clause (e.g. the handler body "{@code S}").
 */
class CatchClause(val decl:DeclarationStatement, val block:BlockStatement)
