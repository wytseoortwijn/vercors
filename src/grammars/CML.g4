grammar CML;

import C;


contract : contractClause+ ;

contractClause
 : 'requires' resource ';'
 | 'ensures' resource ';'
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
