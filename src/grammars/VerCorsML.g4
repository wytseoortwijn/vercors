grammar VerCorsJML;

resourceExpression
 : Identifier ':' resourceExpression
 | expression '?' resourceExpression ':' resourceExpression
 | resourceExpression '**' resourceExpression
 | resourceExpression '-*' resourceExpression 
 | expression '==>' resourceExpression
 | 'ArrayPerm' '(' expression ',' expression ',' expression ',' expression ',' expression ')'
 | 'AddsTo' '(' expression ',' expression ')'
 | 'Perm' '(' expression ',' expression ')'
 | 'PointsTo' '(' expression ',' expression ',' expression ')'
 | 'Value' '(' expression ')'
 | 'Volatile' '(' expression ')'
 | '(' '\\forall*' type Identifier ';' expression ';' resourceExpression ')'
 | '(' resourceExpression ')'
 | specificResourceExpression
 | expression
 ;

specificationPrimary
    : '\\old' '(' expression ')'
    | '\\result'
    | type '{' expressionList? '}'
    | '(' '\\forall' type Identifier ';' expression ';' resourceExpression ')'
    | '(' '\\exists' type Identifier ';' expression ';' resourceExpression ')'
    | '[' expressionList? ']'
    | '|' expression '|'
    | '\\length' '(' expression ')'
    | '*'
    ;
    
expressionList
    :   labeledExpression (',' labeledExpression)*
    ;

labeledExpression
    : ( Identifier ':' )? expression
    ;

 specificationPrimitiveType
    : 'frac'
    | 'zfrac'
    | 'resource'
    | 'classtype'
    ;
 
 