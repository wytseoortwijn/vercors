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
    | 'assert' resourceExpression ';'
    ;    

specificResourceExpression : EOF EOF ;

resource
 : resource '**' resource
 | expression '==>' resource
 | 'perm' '(' expression ',' expression ')'
 | expression
 ;
 
 type
   : specificationPrimitiveType
   | typeName
   ;
 