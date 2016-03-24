grammar VerCorsJML;

resourceExpression
 : Identifier ':' resourceExpression
 | expression '?' resourceExpression ':' resourceExpression
 | resourceExpression '**' resourceExpression
 | resourceExpression '-*' resourceExpression 
 | expression '==>' resourceExpression
 | 'ArrayPerm' '(' expression ',' expression ',' expression ',' expression ',' expression ')'
 | 'AddsTo' '(' expression ',' expression ')'
 | 'Hist' '(' expression ',' expression ',' expression ')'
 | 'Perm' '(' expression ',' expression ')'
 | 'HPerm' '(' expression ',' expression ')'
 | 'PointsTo' '(' expression ',' expression ',' expression ')'
 | 'Reducible' '(' expression ',' ('+' | Identifier ) ')'
 | 'Contribution' '(' expression ',' expression ')'
 | 'Value' '(' expression ')'
 | 'Volatile' '(' expression ')'
 | '(' '\\forall*' type Identifier ';' expression ';' resourceExpression ')'
 | '(' resourceExpression ')'
 | specificResourceExpression
 | '[' expression ']' resourceExpression
 | expression
 ;

specificationPrimary
    : '\\old' '(' expression ')'
    | '\\id' '(' expression ')'
    | '\\result'
    | type '{' expressionList? '}'
    | '(' '\\forall' type Identifier ';' expression ';' resourceExpression ')'
    | '(' '\\exists' type Identifier ';' expression ';' resourceExpression ')'
    | '(' '\\let' type Identifier '=' expression ';' resourceExpression ')'
    | '(' '\\sum' type Identifier ';' expression ';' expression ')'
    | '[' expressionList? ']'
    | '|' expression '|'
    | '\\length' '(' expression ')'
    | '\\unfolding' resourceExpression '\\in' expression
    | '(' expression '!' Identifier ')'
    | '(' expression '\\memberof' expression ')'
    | '['  expression '..' expression ')'
    | '*'
    | '\\current_thread'
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
    | 'process'
    | 'void'
    ;
 
 
