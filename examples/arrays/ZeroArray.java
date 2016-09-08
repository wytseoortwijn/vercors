// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases ZeroArrayLoop
//:: tools silicon
//:: verdict Pass

/**
  This example can in principle work with Chalice, but
  Chalice doe snto support the option<?> type yet.
*/

public class ZeroArray {
    /*@ 
        invariant ar!=null;
        invariant (\forall* int k ; 0 <= k && k < ar.length ; Perm(ar[k],1));
        ensures (\forall int k ; 0 <= k && k < ar.length ; ar[k]==0 ) ;
     */
    public void zero_array(int ar[]){
        int i=0;
        int N=ar.length;
        //@ loop_invariant 0<= i && i<=N && N==ar.length ;
        //@ loop_invariant (\forall int k ; 0 <= k && k < i ; ar[k]==0 ) ;
        while(i<N){
            ar[i]=0;
            i++;
        }
    }

}
