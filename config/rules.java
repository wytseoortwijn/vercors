class silver_optimize {
/*@
  int e1,e2,e3,e4,e5,e6,e7,e8;
  int i;
  
  axiom S1 { ( e1 \memberof [ e2 .. e3 )) ==  ( e2 <= e1 && e1 < e3 ) }
  
  axiom head1 { head (e1) == e1[0] }

//  axiom move_implication {
//     (e1 ==> (\forall* int i; e2 ; e3 ))
//     ==
//     (\forall* int i; e1 && e2 ; e3 )
//  }
*/
}

class simplify_expr {
/*@
  int x;
  
  axiom aunitr { x+0 == x }
  axiom aunitl { 0+x == x }
  
  axiom munitr { x*1 == x }
  axiom munitl { 1*x == x }

  int i;
  boolean b1,b2;
  int e1;

  axiom single_b { (\forall int i; b1 ; (i == (e1!i)) ==> b2 )
               ==
                 (\let int i=e1 ; b1 ==> b2 ) }

  resource r1;
  axiom single_r { (\forall* int i; b1 ; (i == (e1!i)) ==> r1 )
               ==
                 (\let int i=e1 ; b1 ==> r1 ) }

*/
}


class simplify_quant_pass1 {
/*@
  int e1,e2,e3,e4,e5,e6,e7,e8;
  boolean b1,b2,b3,b4;
  resource r1,r2;
  int i,j,k;
  
  axiom aunitr { e1+0 == e1 }
  axiom aunitl { 0+e1 == e1 }
  
  axiom munitr { e1*1 == e1 }
  axiom munitl { 1*e1 == e1 }
  
  axiom I2 {
    0 * e1 == 0
  }
  axiom I3 {
    e1 * 0 == 0
  }
  
  axiom I1 {
    e1 * e2 + e2 == (e1+1) * e2
  }

  axiom sub_0 { e1 - 0 == e1 }
  
  axiom div_1 { ( 1 / e1 ) * e2 == e2 / e1 }
  axiom div_2 { e2 * ( 1 / e1 ) == e2 / e1 }
  
  axiom div_3 { e1 / e1 == 1 }
  axiom div_4 { e1 / 1 == e1 }
  

  axiom B1 {
    true && b1 == b1
  }
  
  axiom B2 {
    false && b1 == b1
  }
  
  axiom A2 {
    e1 <= e2 && e2 < e3 == (e2 \memberof [e1..e3))
  }
  
  axiom A3 {
    (\forall int i; b1 ; (\forall int j; (b2!j) && b3 ; b4 ) )
      ==
    (\forall int i; b1 && b2 ; (\forall int j; b3 ; b4 ) )
  }
  axiom A3r {
    (\forall* int i; b1 ; (\forall* int j; (b2!j) && b3 ; b4 ) )
      ==
    (\forall* int i; b1 && b2 ; (\forall* int j; b3 ; b4 ) )
  }

  axiom single_r { (\forall* int i; b1 ; (i == (e1!i)) ==> r1 )
               ==
                 (\let int i=e1 ; b1 ==> r1 ) }

  axiom A4 {
    (\forall* int i; b1 ; b2 ==> b4 ) 
      ==
    (\forall* int i; b1 && b2 ; b4 ) 
  }
  
  axiom A4b {
    (\forall int i; b1 ; b2 ==> b4 ) 
      ==
    (\forall int i; b1 && b2 ; b4 ) 
  }
  
  axiom A5 {
    (i \memberof [e1 .. e2)) && i > e3
      ==
    (i \memberof [e1<=e3?e3+1:e1 .. e2))
  }
  
  axiom A6 {
    (i \memberof [e1 .. e2)) && i < e3
      ==
    (i \memberof [e1 .. e3<e2?e3:e2))
  }
  
  axiom A7 {
    (\forall* int i; b1 ; Value((e1!i)) ) 
      ==
    Value(e1)
  }
  
  axiom A1 {
    (\forall int i; (i \memberof [ e1 .. e2 )) ; (b1!i))
      ==
    e1 < e2 ==> b1
  }
  
@*//*

  axiom A1 {
    (\forall int i; b1 ; (b2!i))
    ==
    ((\exists int i; true ; b1 ) ==> b2)
  }

*//*@

  int ar[];
  
  
//  axiom deindex2 {
//    (\forall* int i; e1 ; Perm(ar[ this.multidim_index_2(e2,e3,e4,e5) ], e6 ))
//    ==
//    (\forall* int i; e1 ; Perm(ar[ e4*e3 + e5 ], e6 ))
//  }
  
  axiom perm_any {
    Perm(ar[*],e1) == (\forall* int i_fresh ; 0 <= i_fresh && i_fresh < ar.length ; Perm(ar[i_fresh],e1))
  }
  
  axiom array_perm {
    ArrayPerm(ar,e1,e2,e3,e4)
     ==
    (\forall* int i_fresh ; 0 <= i_fresh && i_fresh < e3 ; Perm(ar[e2 * i_fresh + e1],e4))
  }

  axiom single_b { (\forall int i; b1 ; (i == (e1!i)) ==> b2 )
               ==
                 (\let int i=e1 ; b1 ==> b2 ) }

   axiom inlist { (\forall* int i; e1 <= i && i < e2 ; r1 )
                 ==
                 (\forall* int i;  ( i \memberof [ e1 .. e2 )) ; r1 ) }
                 
   axiom inlistb { (\forall int i; e1 <= i && i < e2 ; b1 )
                 ==
                 (\forall int i;  ( i \memberof [ e1 .. e2 )) ; b1 ) }

   axiom LEFTPLUS { (\forall* int i;( i \memberof [ e1 .. e2 )) ; Perm( ar [ (e3!i)+i ] , (e4!i) ) )
                 ==
                 (\forall* int i;  ( i \memberof [ e3+e1 .. e3+e2 )) ; Perm( ar [ i ] , e4 ) ) }

   axiom LEFTPLUS2 { (\forall* int i;( i \memberof [ e1 .. e2 )) ;
                        (\forall* int j ; (j \memberof [(e5!i)..(e6!i))) ;
                        Perm( ar [ (e3!i)+i ] , e4 ) ))
                 ==
                   (\forall* int j ; (j \memberof [e5..e6)) ;
                 (\forall* int i;  ( i \memberof [ e3+e1 .. e3+e2 )) ; Perm( ar [ i ] , e4 ) ))
                  }

   axiom constant { (\forall* int i;( i \memberof [ e1 .. e2 )) ; Perm( (e3!i) , (e4!i) ) )
                 ==
                   Perm(e3,e4*(e2-e1)) }

   axiom right_plus { (\forall* int i;( i \memberof [ e1 .. e2 )) ; Perm( ar [ i+(e3!i) ] , (e4!i) ) )
                 ==
                 (\forall* int i;  ( i \memberof [ e1+e3 .. e2+e3 )) ; Perm( ar [ i ] , e4 ) ) }
                 
   axiom minus { (\forall* int i;( i \memberof [ e1 .. e2 )) ; Perm( ar [ i-(e3!i) ] , (e4!i) ) )
                 ==
                 (\forall* int i;  ( i \memberof [ e1-e3 .. e2-e3 )) ; Perm( ar [ i ] , e4 ) ) }
                 
   axiom left_plusb { (\forall int i;( i \memberof [ e1 .. e2 )) ; ar [ (e3!i) + i ] == (e4!i) )
                 ==
                 (\forall int i;  ( i \memberof [ e3+e1 .. e3+e2 )) ; ar [ i ] == e4 ) }


   axiom nested_bool_1_a_00 {
        (\forall int i;( i \memberof [ 0 .. e1 )) ;
           (\forall int j;( j \memberof [ 0 .. e2 )) ;
              ar[ i * ((e3!i)!j) + j ] == \old(ar[ i * e3 + j ]) ))
    ==
       e2 <= e3 &&
       (\forall int k_fresh;(k_fresh \memberof [ 0 .. e1*e3)) && (k_fresh % e3 < e2);
          ar[k_fresh] == \old(ar[k_fresh]) )
   }
   


   axiom nested_bool_1 {
        (\forall int i;( i \memberof [ 0 .. e1 )) ;
           (\forall int j;( j \memberof [ 0 .. e2 )) ;
              ar[ e3 + j ] == ((e4!i)!j) ))
    ==
       (\forall int k_fresh;(k_fresh \memberof [ 0 .. e1*e2));
          (\let int i=k_fresh/e2 ; (\let int j=k_fresh%e2 ;
//             ( i \memberof [ 0 .. e1 )) && ( j \memberof [ 0 .. e2 )) && ar[ e3 + j ] == e4 )))
             ar[ e3 + j ] == e4 )))
   }
   
   axiom nested_bool_2 {
        (\forall int j;( j \memberof [ 0 .. e2 )) ;
          (\forall int i;( i \memberof [ 0 .. e1 )) ;
              ar[ e3 + j ] == e4 ))
    ==
       (\forall int k_fresh;(k_fresh \memberof [ 0 .. e1*e2));
          (\let int i=k_fresh/e2 ; (\let int j=k_fresh%e2 ;
//            ( i \memberof [ 0 .. e1 )) && ( j \memberof [ 0 .. e2 )) && ar[ e3 + j ] == e4 )))
            ar[ e3 + j ] == e4 )))
   }

   axiom nested_bool_1_a_0 {
        (\forall int i;( i \memberof [ 0 .. e1 )) ;
           (\forall int j;( j \memberof [ 0 .. e2 )) ;
              (ar[ i * ((e3!i)!j) + j ] \memberof ((e4!i)!j)) ))
    ==
       e2 <= e3 &&
       (\forall int k_fresh;(k_fresh \memberof [ 0 .. e1*e3)) && (k_fresh % e3 < e2);
          (ar[k_fresh] \memberof e4))
   }
   
//   axiom nested_bool_1_a {
//        (\forall int i;( i \memberof [ 0 .. e1 )) ;
//           (\forall int j;( j \memberof [ 0 .. e2 )) ;
//              (ar[ e3 + j ] \memberof e4) ))
//    ==
//       (\forall int k_fresh;(k_fresh \memberof [ 0 .. e1*e2));
//          (\let int i=k_fresh/e2 ; (\let int j=k_fresh%e2 ;
//             (ar[ e3 + j ] \memberof e4) )))
//   }
   
   axiom nested_bool_2_a {
        (\forall int j;( j \memberof [ 0 .. e2 )) ;
          (\forall int i;( i \memberof [ 0 .. e1 )) ;
              (ar[ e3 + j ] \memberof e4) ))
    ==
       (\forall int k_fresh;(k_fresh \memberof [ 0 .. e1*e2));
          (\let int i=k_fresh/e2 ; (\let int j=k_fresh%e2 ;
            (ar[ e3 + j ] \memberof e4) )))
   }

   axiom div_mod {
     (e1 / e2) * e2 + (e1 % e2) == e1
   }
   

   axiom reorder_1 {
     ( j \memberof ([ e3 * i .. e3 * (i + 1) )))
       ==
     ( j \memberof ([ i * e3 .. (i + 1) * e3 )))
   }

   axiom nested_1 {
        (\forall* int i;( i \memberof ([ e1 .. e2 )) );
            (\forall* int j;( j \memberof ([ i * e3 .. (i + 1) * e3 )) );
                (r1!i) ))
        ==
        (\forall* int j;( j \memberof ([ e1 * e3 .. e2 * e3 )) ); r1 )
        }
        
   axiom nested_Z1 {
        (\forall* int i;( i \memberof ([ e1 .. e2 )) );
            (\forall* int j;( j \memberof ([ 0 .. e3 )) );
                Perm( ar[e5 + (i*e3+j) ] , ((e4!i)!j) ) ))
        ==
        (\forall* int j;( j \memberof ([ e1 * e3 .. e2 * e3 )) ); Perm(ar[e5+j],e4) )
        }

   axiom nested_Z1_x {
        (\forall* int i;( i \memberof ([ e1 .. e2 )) ) && e6;
            (\forall* int j;( j \memberof ([ 0 .. e3 )) );
                Perm( ar[e5 + (i*e3+j) ] , ((e4!i)!j) ) ))
        ==
        (\forall* int j;( j \memberof ([ e1 * e3 .. e2 * e3 )) ) && e6; Perm(ar[e5+j],e4) )
        }

   axiom nested_x1 {
        (\forall* int i;( i \memberof ([ e1 .. e2 )) );
            (\forall* int j;( j \memberof ([ i * e3 .. i * e3 + e4)) );
                (r1!i) ))
        ==
          (e4 <= e3) **
        (\forall* int j;( j \memberof ([ e1 * e3 .. e2 * e3 )) ) && (j % e3 < e4); r1 )
        }
        
   axiom nested_1b {
        (\forall int i;( i \memberof ([ e1 .. e2 )) );
            (\forall int j;( j \memberof ([ i * e3 .. (i + 1) * e3 )) );
                (b1!i) ))
        ==
        (\forall int j;( j \memberof ([ e1 * e3 .. e2 * e3 )) ); b1 )
        }
        
   axiom nested_x1b {
        (\forall int i;( i \memberof ([ e1 .. e2 )) );
            (\forall int j;( j \memberof ([ i * e3 .. i * e3 + e4)) );
                (b1!i) ))
        ==
          (e4 <= e3) **
        (\forall int j;( j \memberof ([ e1 * e3 .. e2 * e3 )) ) && (j % e3 < e4); b1 )
        }
        
        
   axiom nested_2 {
        (\forall* int i;( i \memberof ([ e1 .. e2 )) );
            (\forall* int j;( j \memberof ([ ((e4!i) + i) * e3 .. (e4 + i + 1) * e3 )) );
                (r1!i) ))
        ==
        (\forall* int j;( j \memberof ([ (e4 + e1) * e3 .. (e4 + e2) * e3 )) ); r1 )
        }
        
   axiom nested_2x {
        (\forall* int i;( i \memberof ([ e1 .. e2 )) );
          (\forall* int k ; (b1!i) ;
            (\forall* int j;( j \memberof ([ ((e4!i) + i) * e3 .. (e4 + i + 1) * e3 )) );
                (r1!i) )))
        ==
          (\forall* int k ; b1 ;
        (\forall* int j;( j \memberof ([ (e4 + e1) * e3 .. (e4 + e2) * e3 )) ); r1 ))
        }
        
    axiom lin1 {
        (\forall* int i;( i \memberof [ e1 * (e2!i) * (e3!i) .. e4 )) ; r1 )
           ==
        (\forall* int i;( i \memberof [ e1 * (e2*e3) .. e4 )) ; r1 )
    }
    
    axiom lin2 {
        (\forall* int i;( i \memberof [ e4 .. e1 * (e2!i) * (e3!i))) ; r1 )
           ==
        (\forall* int i;( i \memberof [ e4 .. e1 * (e2*e3))) ; r1 )
    }
    
    axiom split1 {
       (\forall* int i;e1;e2**e3)
         ==
       (\forall* int i;e1;e2) ** (\forall* int i;e1;e3)
    }
        
    axiom split2 {
       (\forall* int i;e1;PointsTo(e2,e3,e4))
         ==
       (\forall* int i;e1;Perm(e2,e3)) ** (\forall int i;e1;e2==e4)
    }
        
*/
}

class simplify_quant_pass2 {
/*@
  int e1,e2,e3,e4,e5,e6,e7,e8;
  boolean b1,b2,b3,b4;
  resource r1,r2;
  int i,j,k;
  
  int ar[];
  
  axiom aunitr { e1+0 == e1 }
  axiom aunitl { 0+e1 == e1 }
  
  axiom munitr { e1*1 == e1 }
  axiom munitl { 1*e1 == e1 }
  
  axiom I2 {
    0 * e1 == 0
  }
  axiom I3 {
    e1 * 0 == 0
  }

  // simplify x*a+b index.
  // PROBLEM: this is wrong if e3 < 0!
  axiom simplify_linear_ab {
    (\forall* int i;( i \memberof [ e1 .. e2 )) ; Perm( ar [ i*(e3!i) +(e4!i) ] , (e5!i) ))
     ==
    (\forall* int i;( i \memberof [ e1*e3+e4 .. e2*e3+e4 )) && (i - e4) % e3 == 0 ; Perm( ar [ i ] , e5 ))
  }
  
  // completion for b==0.
  axiom simplify_linear_a {
    (\forall* int i;( i \memberof [ e1 .. e2 )) ; Perm( ar [ i*(e3!i)] , (e5!i) ))
     ==
    (\forall* int i;( i \memberof [ e1*e3 .. e2*e3 )) && i % e3 == 0 ; Perm( ar [ i ] , e5 ))
  }
  
  // completion for a==1.
  axiom simplify_linear_b {
    (\forall* int i;( i \memberof [ e1 .. e2 )) ; Perm( ar [ i +(e4!i) ] , (e5!i) ))
     ==
    (\forall* int i;( i \memberof [ e1+e4 .. e2+e4 )) ; Perm( ar [ i ] , e5 ))
  }
  
  axiom simplify_shift_1 {
    (\forall* int i; b1 ; Perm( ar [ (e1!i) + i ] , (e2!i) ))
      ==
    (\forall* int k_fresh ; (\let int i=k_fresh-e1;b1) ; Perm( ar [ k_fresh ] , e2 ))
  }
  
  axiom simplify_shift_2 {
    (\forall* int i; b1 ; Perm( ar [ i + (e1!i) ] , (e2!i) ))
      ==
    (\forall* int k_fresh ; (\let int i=k_fresh-e1;b1) ; Perm( ar [ k_fresh ] , e2 ))
  }
  
  axiom simplify_shift_3 {
    (\forall* int i; b1 ; Perm( ar [ i - (e1!i) ] , (e2!i) ))
      ==
    (\forall* int k_fresh ; (\let int i=k_fresh+e1;b1) ; Perm( ar [ k_fresh ] , e2 ))
  }
  
  axiom simplify_shift_scale_1 {
    (\forall* int i; b1 ; Perm( ar [ (e1!i) + i * (e2!i) ] , (e3!i) ))
      ==
    (\forall* int k_fresh ; (\let int i=(k_fresh/e2)-e1;b1) && k_fresh % e2 == 0; Perm( ar [ k_fresh ] , e3 ))
  }
 
@*/

}


class summation {

/*@
    int i,j,v;
    seq<int> ar;
    int e1,e2,e3,e4,e5;
    
    
//    axiom deindex2 {
//      (\sum int i; e1 ; ar[ this.multidim_index_2(e2,e3,e4,e5) ])
//    ==
//      (\sum int i; e1 ; ar[ e4*e3 + e5 ])
//    }

    axiom sum1 {
        (\sum int i ; ( i \memberof [ e1 .. e2 )) ; ar[i])
          ==
        sum_array(e1,e1,e2,ar)
    }
    
    axiom sum2 {
        (\sum int i ; ( i \memberof [ e1 .. e2 )) ; (ar[i]==(v!i))?1:0)
          ==
        count_list(e1,e2,ar,v)
    }
    
    axiom sum2b {
        (\sum int i ; true ;
          (\sum int j ; ( i \memberof [ 0 .. e1 )) && (j \memberof [ 0 .. e2 )) ; (ar[i*e2 + j]==(v!i))?1:0))
          ==
        count_array(0,e1*e2,ar,v)
    }
    
    axiom sum2c {
        (\sum int i ; ( i \memberof [ 0 .. e1 )) ;
          (\sum int j ; ( j \memberof [ 0 .. e2 )) ; (ar[i*e2 + j]==(v!i))?1:0))
          ==
        count_array(0,e1*e2,ar,v)
    }

    axiom sum3b {
        (\sum int i ; true ;
          (\sum int j ; ( i \memberof [ 0 .. e1 )) && (j \memberof [ 0 .. e2 )) ; (ar[i*e3 + j]==(v!i))?1:0))
          ==
        count_square(0,0,e2,e3,0,e1*e3,ar,v)
    }
   
    axiom sum3c {
        (\sum int i ; ( i \memberof [ 0 .. e1 )) ;
          (\sum int j ; ( j \memberof [ 0 .. e2 )) ; (ar[i*e3 + j]==(v!i))?1:0))
          ==
        count_square(0,0,e2,e3,0,e1*e3,ar,v)
    }

  requires 0 <= i && i <= hi;
  requires hi <= |ar|;
  static int sum_list(int i,int hi,seq<int> ar) = (i < hi ? (ar[i] + sum_list(i+1,hi,ar)) : 0 );

  requires 0 <= lo && lo <= i && i <= hi;
  requires (\forall* int k ; lo <= k && k < hi ; Value(ar[k]));
  static int sum_array(int i,int lo,int hi,int ar[]) = (i < hi ? (ar[i] + sum_array(i+1,lo,hi,ar)) : 0 );

  requires 0 <= lo && lo <= hi && hi <= step && step > 0;
  requires 0 <= min && min <= i && i <= max;
  requires (\forall* int k ; min <= k && k < max && lo <= (k % step) && (k % step) < hi ; Value(ar[k]));
  static int sum_square(int i,int lo,int hi,int step,int min,int max,int ar[])=
    (i < max ?  ( lo <= (i % step) && (i% step) < hi ? ar[i] : 0 ) + sum_square(i+1,lo,hi,step,min,max,ar) : 0 );

  requires 0 <= lo && lo <= hi && hi <= step && step > 0;
  requires 0 <= min && min <= i && i <= max;
  requires (\forall* int k ; min <= k && k < max && lo <= (k % step) && (k % step) < hi ; Value(ar[k]));
  static int count_square(int i,int lo,int hi,int step,int min,int max,int ar[],int v)=
    (i < max ?  ( lo <= (i % step) && (i% step) < hi && ar[i] == v ? 1 : 0 ) + count_square(i+1,lo,hi,step,min,max,ar,v) : 0 );

  requires 0 <= i && i <= hi;
  requires hi <= |ar|;
  static int count_list(int i,int hi,seq<int> ar,int v) = (i < hi ? ((ar[i]==v?1:0) + count_list(i+1,hi,ar,v)) : 0 );
  
  requires 0 <= i && i <= hi;
  requires (\forall* int k ; 0 <= k && k < hi ; Value(ar[k]));
  static int count_array(int i,int hi,int ar[],int v) = (i < hi ? ((ar[i]==v?1:0) + count_array(i+1,hi,ar,v)) : 0 );

@*/

}

class chalice_optimize {
/*@
    int i;
    seq<cell<int>> ar;
    int e;
    
    axiom array_perm {
      (\forall* int i; 0 <= i && i < |ar| ; Perm(ar[i].item , (e!i)))
      ==
      Perm(ar[*].item,e) ** (\forall int i; 0 <= i && i < |ar| ; ar[i] != null)
    }

*/
}

