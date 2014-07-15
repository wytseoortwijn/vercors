grammar CML;

import VerCorsML, C;

specificationSequence : ( specificationStatement)* contract? ;

contract : contractClause+ ;

contractClause
 : 'requires' resourceExpression ';'
 | 'ensures' resourceExpression ';'
 ;


specificationStatement
    : 'loop_invariant' resourceExpression ';'        
    | 'send' resourceExpression 'to' Identifier ',' expression ';'
    | 'recv' resourceExpression 'from' Identifier ',' expression ';'
    | 'assert' resourceExpression ';'
    ;    

// For C there are no specific resource expressions:
specificResourceExpression : EOF EOF ;

// extend original type defininition with specification only types:
type
   : specificationPrimitiveType
   | typeName
   ;
 