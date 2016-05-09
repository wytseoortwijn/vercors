grammar omp;

@header {
package vct.parsers;
}


omp_pragma : omp_parallel | omp_parallel_for | omp_for ;

omp_parallel_for : 'parallel' 'for' omp_option* ;
omp_for : 'for' omp_option* ;

omp_parallel : 'parallel' omp_option ;

omp_option : omp_private | omp_nowait ;

omp_private : 'private' '(' id_list ')' ;

omp_nowait : 'nowait' ;
 
id_list : ( Identifier ( ',' Identifier )* )? ;

Identifier : [a-zA-Z_] ([0-9a-zA-Z_])* ;

WhiteSpace
        :   (   ' '
        |   '\t'
        |   '\r'
        |   '\n'
        )+ -> skip ;
