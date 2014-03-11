grammar CML;

import C;

specificationSequence : ( specificationStatement)* contract? ;

contract : contractClause+ ;

contractClause
 : 'requires' resource ';'
 | 'ensures' resource ';'
 ;

specificationStatement
    : 'loop_invariant' resource ';'
    ;    
    
resource
 : resource '**' resource
 | expression '==>' resource
 | 'perm' '(' expression ',' expression ')'
 | expression
 ;

primaryExpression
    :   Identifier
    |   Constant
    | 'old'  '(' expression ')'
    ;
 