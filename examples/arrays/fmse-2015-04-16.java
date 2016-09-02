// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases FMSE-2015-04-16-Ex4
//:: tools silicon
//:: verdict Pass

/*
  Answer to question 4 of the FMSE exam on April 16, 2015.
*/

class Exercise4 {
  
  /*@
     requires a!=null && b != null && res != null;
     requires a.length==b.length && res.length==2*a.length;
     requires (\forall* int i ; 0 <= i && i < a.length ; Perm(a[i],1));
     requires (\forall* int i ; 0 <= i && i < b.length ; Perm(b[i],1));
     requires (\forall* int i ; 0 <= i && i < res.length ; Perm(res[i],1));
     ensures a.length==b.length && res.length==2*a.length;
     ensures (\forall* int i ; 0 <= i && i < a.length ; Perm(a[i],1));
     ensures (\forall* int i ; 0 <= i && i < b.length ; Perm(b[i],1));
     ensures (\forall* int i ; 0 <= i && i < res.length ; Perm(res[i],1));
     ensures (\forall int i ; 0 <= i && i < a.length ; res[2*i]==a[i] );
     ensures (\forall int i ; 0 <= i && i < b.length ; res[2*i+1]==b[i] );
   */
  void zip(int[] a, int[] b, int[] res) {
    int k = 0;
    /*@
      loop_invariant a!=null && b != null && res != null;
      loop_invariant 0 <= k ** k%2 ==0 ** k <= res.length ** a.length==b.length ** res.length==2*a.length;
      loop_invariant (\forall* int i ; 0 <= i && i < a.length ; Perm(a[i],1));
      loop_invariant (\forall* int i ; 0 <= i && i < b.length ; Perm(b[i],1));
      loop_invariant (\forall* int i ; 0 <= i && i < res.length ; Perm(res[i],1));
      loop_invariant (\forall int i ; 0 <= i && i < k/2 ; res[2*i]==a[i] );
      loop_invariant (\forall int i ; 0 <= i && i < k/2 ; res[2*i+1]==b[i] );      
     */
    while (k < res.length) {
      res[k] = a[k/2];
      res[k+1] = b[k/2];
      k = k+2;
    }
  }
  
}

