// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases ZeroArrayNested
//:: tools silicon
//:: verdict Pass

/**
  vct --silver=silicon_qp ZeroMatrixNested.java
  should say:
  PASS
*/

public class Ref {


    /*@ 
        invariant ar != null;
        requires M>0 ** N > 0 ** M * N == ar.length;
        requires (\forall* int k ; 0 <= k && k < ar.length ; Perm(ar[k],write));
        ensures  (\forall* int k ; 0 <= k && k < ar.length ; Perm(ar[k],write));
        ensures  (\forall  int k ; 0 <= k && k < ar.length ; ar[k]==0 ) ;
     */
    public void zero_array(int ar[],int M,int N){
        for(int i=0;i<M;i++)
          /*@
            requires M * N == ar.length;
            requires (\forall* int k ; i*N <= k && k < (i+1)*N ; Perm(ar[k],write));
            ensures  (\forall* int k ; i*N <= k && k < (i+1)*N ; Perm(ar[k],write));
            ensures  (\forall  int k ; i*N <= k && k < (i+1)*N ; ar[k]==0 ) ;
          */
        {
          for(int j=0;j<N;j++)
          /*@
            requires 0 <= i && i < M && M * N == ar.length;
            requires Perm(ar[i*N+j],write);
            ensures  0 <= i && i < M && M * N == ar.length;
            ensures  Perm(ar[i*N+j],write);
            ensures  ar[i*N+j]==0;
          @*/
          {
            ar[i*N+j]=0;
          }
        }
    }

}

