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
  | <assoc=right> type '->' type
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
    | 'modifies' expressionList ';'
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
    | 'refute' resourceExpression ';'
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
    | 'send' resourceExpression 'to' Identifier ',' expression ';'
    | 'recv' resourceExpression 'from' Identifier ',' expression ';'
    | 'transfer' resourceExpression ';'
    | 'action' resourceExpression ',' resourceExpression ';'
    | 'create' resourceExpression ',' resourceExpression ';'
    | 'destroy' resourceExpression ',' resourceExpression ',' resourceExpression ';'
    ;

proofScript :
    ( 'label' Identifier | 'with' block | 'then' block )*
    ;

specificationDeclaration
    : classBodyDeclaration
    | functionDeclaration
    | axiomDeclaration
    ;
    
functionDeclaration
    : modifier* type Identifier formalParameters '=' resourceExpression ';' 
    ;

axiomDeclaration
    : 'axiom' Identifier '{' resourceExpression '==' resourceExpression '}'
    ;
