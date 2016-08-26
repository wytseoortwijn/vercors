grammar omp;

@header {
package vct.parsers;
}


omp_pragma
 : omp_parallel
// task generating constructs
 | omp_for
 | omp_single
 | omp_sections
// other constructs.
 | omp_section
// composite constructs.
 | omp_parallel_for
 ;

omp_parallel : 'parallel' omp_option* ;

omp_for : 'for' omp_option* ;

omp_single : 'single' omp_option* ;

omp_sections : 'sections' omp_option* ;

omp_section : 'section' omp_option* ;

omp_parallel_for : 'parallel' 'for' omp_option* ;

omp_option : omp_private | omp_nowait | omp_schedule ;

omp_schedule : 'schedule' '(' 'static' ')' ;

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
