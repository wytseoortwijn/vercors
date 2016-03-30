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
    | 'inline'
    | 'thread_local'
    ;

specificationStatement
    : 'requires' resourceExpression ';'
    | 'ensures' resourceExpression ';'
    | 'modifies' expressionList ';'
    | 'given' localVariableDeclaration ';'
    | 'yields' localVariableDeclaration ';'
    | 'loop_invariant' resourceExpression ';'
    | 'fold' resourceExpression ';'
    | 'unfold' resourceExpression ';'
    | 'label' Identifier
    | 'with' block
    | 'proof' block
    | 'then' block
    | 'refute' resourceExpression ';'
    | 'assert' resourceExpression ';'
    | 'exhale' resourceExpression ';'
    | 'inhale' resourceExpression ';'
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
    | 'csl_subject' expression ';'
    | 'action' expression ',' expression ',' expression ',' expression ';'
    | 'create' resourceExpression ';'
    | 'create' resourceExpression ',' resourceExpression ';'
    | 'destroy' resourceExpression ';'
    | 'destroy' resourceExpression ',' resourceExpression ';'
    | 'split' resourceExpression ',' resourceExpression ',' resourceExpression ',' resourceExpression ',' resourceExpression ';'
    | 'merge' resourceExpression ',' resourceExpression ',' resourceExpression ',' resourceExpression ',' resourceExpression ';'
    | '}' 'spec_ignore'
    | 'spec_ignore' '{'
    | 'atomic' '(' expressionList ')' block
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
