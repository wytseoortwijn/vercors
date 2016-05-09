grammar PVFull;

@header {
package pv.parser;
}

@lexer::members{
  public final static int COMMENT=ML_COMMENT;
  public final static int LINEDIRECTION=Integer.MAX_VALUE;
}

program  : (claz|kernel|block|field|method|abs_decl|function)* (block)? ;

claz : contract 'class' ID '{'( field | method | function | constructor | abs_decl )* '}' ;

kernel : 'kernel' ID '{' ( kernel_field | method | function )* '}' ;

kernel_field : ('global' | 'local') type ID ( ',' ID )* ';' ;

field : type ID ( ',' ID )* ';' ;

function : contract modifiers type ID '(' args ')' '=' expr ';' ;

modifiers : ( 'static' | 'thread_local' | 'inline' )*;

method : contract type gen_id '(' args ')' block ;

constructor : contract ID '(' args ')' block ;

abs_decl : contract type ID '(' args ')' ';' ;

contract :
 ( 'modifies' expr ';'
 | 'requires' expr ';'
 | 'ensures' expr ';'
 | 'given' type ID ';'
 | 'yields' type ID ';'
 )*;

args : type ID ( ',' type ID )* | ;

expr
 : lexpr
 | ID ':' expr
 | expr 'with' block 
 | expr 'then' block 
 | CONTAINER '<' type '>' values  
 | ('!'|'-') expr
 | expr '^^' expr
 | expr ('*'|'/'|'%') expr
 | expr ( '+' | '-' ) expr
 | expr ( '<' | '<=' | '>=' | '>') expr
 | expr ( '==' | '!=' ) expr
 | expr ('&&' | '**') expr
 | expr ('||' | '==>') expr
 | expr 'in' expr
 | expr '?' expr ':' expr
 | '?' ID
 | 'unfolding' expr 'in' expr 
 | lexpr '->' ID tuple
 | (lexpr | 'Value' | 'Perm' | 'PointsTo' | 'Hist' | '\\old' | '?' ) tuple
 | '(' ('\\sum' | '\\exists' | '\\forall' | '\\forall*') type ID ';' expr (';' expr )? ')'
 | '(' expr ')'
 | '\\owner' '(' expr ',' expr ',' expr ')'
 | 'id' '(' expr ')'
 | 'new' ID tuple
 | 'new' type '[' expr ']'
 | 'null'
 | 'true'
 | 'false'
 | '\\result'
 | 'current_thread'
 | ID
 | NUMBER
 | '[' expr ']' expr
 | '|' expr '|'
 | values
 ;

values : '{' ( | expr (',' expr)*) '}';

tuple : '(' ( | expr (',' expr)*) ')';

block : '{' statement* '}' ;

statement
 : 'return' expr ';'
 | 'lock' expr ';'
 | 'unlock' expr ';'
 | 'wait' expr ';'
 | 'notify' expr ';'
 | 'fork' expr ';'
 | 'join' expr ';'
 | 'fold' expr ';'
 | 'unfold' expr ';'
 | 'assert' expr ';' 
 | 'assume' expr ';' 
 | 'witness' expr ';' 
 | 'if' '(' expr ')' block ( 'else' block )?
 | 'barrier' '(' ID ( ';' id_list )? ')' ( '{' contract '}' | contract block )
 | 'par' par_unit ( 'and' par_unit )* 
 | 'invariant' ID '(' expr ')' block 
 | 'atomic' '(' id_list ')' block 
 | invariant 'while' '(' expr ')' block
 | type ID ('=' expr | (',' ID)* ) ';'
 | expr ';'
 | block
 | lexpr '=' expr ';'
 | '{*' expr '*}'
 | 'action' expr ',' expr block 
 | 'create' expr ',' expr ';'
 | 'destroy' expr ',' expr ',' expr ';'
 | 'goto' ID ';'
 | 'label' ID ';'
 ;

par_unit
 : ID? '(' iters ')' contract block
 | contract block
 ;

id_list : ( ID ( ',' ID )* )? ;

with_then : ( 'with' block )? ('then' block)? ;

iters : ( iter ( ',' iter )* )? ;

iter : type ID '=' expr '..' expr ;

decls  : ( decl ( ',' decl )* )? ;

decl : type ID ( '=' expr )? ;

fence_list : ( 'local' | 'global' )* ;

invariant : ( 'loop_invariant' expr ';' )* ;

lexpr : ('this' | '\\result' | ID ) ('.' gen_id | '[' expr ']' )* ; 

type
 : CONTAINER '<' type '>'
 | ( 'process' | 'int' | 'boolean' | 'zfrac' | 'frac' | 'resource' | 'void' | ID | classType ) ('[' expr? ']')*
 ;

gen_id : ID | CONTAINER ; 

classType : ID typeArgs?;

typeArgs : '<' expr (',' expr)* '>';


CONTAINER : 'seq' | 'set' | 'bag' ;

ID  : ('a'..'z'|'A'..'Z') ('a'..'z'|'A'..'Z'|'0'..'9'|'_')*;
NUMBER : ('0'..'9')+;

ML_COMMENT : '/*' .*? '*/' -> channel(ML_COMMENT) ;
SL_COMMENT : '//' .*? '\n' -> channel(ML_COMMENT) ;

WS  :   (   ' '
        |   '\t'
        |   '\r'
        |   '\n'
        )+ -> skip ;

EmbeddedLatex
    : '#' ~[\r\n]* '#' -> skip
    ;
