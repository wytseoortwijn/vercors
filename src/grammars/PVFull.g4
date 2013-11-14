grammar PVFull;

@header {
package pv.parser;
}

@lexer::members{
  public final static int WHITESPACE=1;
  public final static int COMMENT=2;
  public final static int CONTROL=3;
  public final static int LINEDIRECTION=4;
}

program  : (claz|kernel)* (block)? ;

claz : 'class' ID '{'( field | method | function /* | predicate | invariant | function */ )* '}' ;

kernel : 'kernel' ID '{' ( kernel_field | method | function )* '}' ;

kernel_field : ('global' | 'local') type ID ( ',' ID )* ';' ;

field : type ID ( ',' ID )* ';' ;

function : contract type ID '(' args ')' '=' expr ';' ;

method : contract type ID '(' args ')' block ;

contract :
 ( 'requires' expr ';'
 | 'ensures' expr ';'
 | 'given' type ID ';'
 | 'yields' type ID ';'
 )*;

args : type ID ( ',' type ID )* | ;

expr
 : lexpr
 | ('!'|'-') expr
 | expr ('mul'|'div'|'mod') expr
 | expr ( '+' | '-' ) expr
 | expr ( '<' | '<=' | '>=' | '>') expr
 | expr ( '=' | '!=' ) expr
 | expr ('&' | '*') expr
 | expr ('|' | '->') expr
 | expr '?' expr ':' expr
 | (lexpr | 'perm' | 'pointsto' | 'old' ) tuple
 | '(' ('exists'|'forall'|'forall*') type ID ';' expr (';' expr )? ')'
 | '(' expr ')'
 | 'new' ID
 | 'null'
 | 'true'
 | 'false'
 | ID
 | NUMBER
 ;

tuple : '(' ( | expr (',' expr)*) ')';

block : '{' statement* '}' ;

statement
 : 'return' expr ';'
 | 'lock' expr ';'
 | 'unlock' expr ';'
 | 'fork' expr ';'
 | 'join' expr ';'
 | 'fold' expr ';'
 | 'unfold' expr ';'
 | 'assert' expr ';' 
 | 'assume' expr ';' 
 | 'if' '(' expr ')' block ( 'else' block )?
 | 'barrier' '(' fence_list ')' '{' contract '}' 
 | invariant 'while' '(' expr ')' block
 | 'call' lexpr tuple ';'
 | block
 | type ID (':=' expr | (',' ID)* ) ';'
 | lexpr ':=' expr ';'
 ;

fence_list : ( 'local' | 'global' )* ;

invariant : ( 'invariant' expr ';' )* ;

lexpr : ('this' | 'result' | ID ) ('.' ID | '[' expr ']' )* ; 

type : ('int' | ID ) ('[' expr ']')*;

ID  : ('a'..'z'|'A'..'Z') ('a'..'z'|'A'..'Z'|'0'..'9'|'_')*;
NUMBER : ('0'..'9')+;

ML_COMMENT : '/*' .*? '*/' -> channel(COMMENT) ;
SL_COMMENT : '//' .*? '\n' -> channel(COMMENT) ;

WS  :   (   ' '
        |   '\t'
        |   '\r'
        |   '\n'
        )+ -> channel(WHITESPACE) ;

