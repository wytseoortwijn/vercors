grammar JavaJML;

import Java;

specificationSequence : ( specificationDeclaration | statement )* contract? ;

contract : contractClause+ ;

contractClause
 : 'requires' resourceExpression ';'
 | 'ensures' resourceExpression ';'
 | 'given' localVariableDeclaration ';'
 | 'yields' localVariableDeclaration ';'
 ;

resourceExpression
 : expression '->' Identifier '(' expressionList? ')'
 | ( expression . )? Identifier '@' Identifier '(' expressionList? ')'
 | Identifier ':' resourceExpression
 | expression '?' resourceExpression ':' resourceExpression
 | resourceExpression '**' resourceExpression
 | resourceExpression '-*' resourceExpression 
 | expression '==>' resourceExpression
 | 'ArrayPerm' '(' expression ',' expression ',' expression ',' expression ',' expression ')'
 | 'Perm' '(' expression ',' expression ')'
 | 'PointsTo' '(' expression ',' expression ',' expression ')'
 | 'Value' '(' expression ')'
 | '(' resourceExpression ')'
 | expression
 ;

specificationPrimary
    : '\\old' '(' expression ')'
    | '\\result'
    | type '{' expressionList? '}'
    | '(' '\\forall' formalParameter ';' expression ';' resourceExpression ')'
    | '[' expressionList? ']'
    | '*'
    ;
    
type
  : type '[' ']'
  | type ',' type
  | type '->' <assoc=right> type
  | classOrInterfaceType
  | primitiveType
  | '(' type ')'
  ;

arguments
    :   '(' expressionList? ')'
    ;
    
expressionList
    :   labeledExpression (',' labeledExpression)*
    ;

labeledExpression
    : ( Identifier ':' )? expression
    ;

specificationModifier
    : 'pure'
    ;

specificationPrimitiveType
    : 'frac'
    | 'zfrac'
    | 'resource'
    | 'classtype'
    ;

specificationStatement
    : 'loop_invariant' resourceExpression ';'
    | 'set' expression '=' expression ';'
    | 'fold' resourceExpression ';'
    | 'unfold' resourceExpression ';'
    | 'label' Identifier
    | 'with' block
    | 'proof' block
    | 'then' block
    | ASSERT resourceExpression ';'
    | 'assume' resourceExpression ';'
    | 'create' resourceExpression block
    | 'create' block resourceExpression ';'
    | 'create' block
    | 'qed' resourceExpression ';'
    | 'apply' resourceExpression proofScript ';'
    | 'use' resourceExpression ';'
    | 'witness' resourceExpression ';'
    | 'open' resourceExpression block? ';'
    | 'close' resourceExpression ';'
    ;

proofScript :
    ( 'label' Identifier | 'with' block | 'then' block )*
    ;

specificationDeclaration
    : contract? classBodyDeclaration
    | functionDeclaration
    ;
    
functionDeclaration
    : contract? modifier* type Identifier formalParameters '=' resourceExpression ';' 
    ;
