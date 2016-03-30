grammar CML;

import VerCorsML, C;

specificationSequence : ( specificationDeclaration | statement )* contract? ;

contract : contractClause+ ;

contractClause
 : 'requires' resourceExpression ';'
 | 'ensures' resourceExpression ';'
 | 'given' type Identifier ';'
 ;


specificationStatement
    : 'loop_invariant' resourceExpression ';'        
    | 'send' resourceExpression 'to' Identifier ',' expression ';'
    | 'recv' resourceExpression 'from' Identifier ',' expression ';'
    | 'assert' resourceExpression ';'
    ;
    
specificationDeclaration
    : pureFunctionDeclaration
    ;

pureFunctionDeclaration
    : declarationSpecifiers declarator '=' expression ';'
    ;
    
// For C there are no specific resource expressions:
specificResourceExpression : EOF EOF ;

// extend original type defininition with specification only types:
type
   : specificationPrimitiveType
   | typeName
   ;
 