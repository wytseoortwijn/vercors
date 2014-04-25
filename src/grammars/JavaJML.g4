grammar JavaJML;

import VerCorsML, Java;

specificationSequence : ( specificationDeclaration | statement )* ;

specificResourceExpression
 : expression '->' Identifier '(' expressionList? ')'
 | ( expression . )? Identifier '@' Identifier '(' expressionList? ')'
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
    
specificationModifier
    : 'pure'
    ;

specificationStatement
    : 'requires' resourceExpression ';'
    | 'ensures' resourceExpression ';'
    | 'given' localVariableDeclaration ';'
    | 'yields' localVariableDeclaration ';'
    | 'loop_invariant' resourceExpression ';'
    | 'set' expression '=' expression ';'
    | 'fold' resourceExpression ';'
    | 'unfold' resourceExpression ';'
    | 'label' Identifier
    | 'with' block
    | 'proof' block
    | 'then' block
    | 'assert' resourceExpression ';'
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
    : classBodyDeclaration
    | functionDeclaration
    ;
    
functionDeclaration
    : modifier* type Identifier formalParameters '=' resourceExpression ';' 
    ;
