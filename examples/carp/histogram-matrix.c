// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases HistogramMatrix
//:: tools silicon
//:: verdict Pass

/*@
  invariant matrix != NULL && hist != NULL;
  requires M>0 && N > 0 && P > 0;
  requires (\forall* int i1 ; 0 <= i1 && i1 < M ;
             (\forall* int j1 ; 0 <= j1 && j1 < N ;
               Perm(matrix[i1][j1],1/2)));
  requires (\forall int i1 ; 0 <= i1 && i1 < M ;
             (\forall int j1 ; 0 <= j1 && j1 < N ;
               0 <= matrix[i1][j1] && matrix[i1][j1] < P));
  requires (\forall* int i1 ; 0 <= i1 && i1 < P ;
               Perm(hist[i1],write));            
  ensures  (\forall* int i1 ; 0 <= i1 && i1 < M ;
             (\forall* int j1 ; 0 <= j1 && j1 < N ;
               Perm(matrix[i1][j1],1/2)));
  ensures  (\forall* int i1 ; 0 <= i1 && i1 < P ;
               Perm(hist[i1],write));
  ensures  (\forall int k; 0 <= k && k < P ; hist[k]==
               (\sum int i1 ; 0 <= i1 && i1 < M ;
                 (\sum int j1 ; 0 <= j1 && j1 < N ;
                   matrix[i1][j1]==k?1:0)));
  ensures  (\forall int i1 ; 0 <= i1 && i1 < M ;
             (\forall int j1 ; 0 <= j1 && j1 < N ;
               matrix[i1][j1]==\old(matrix[i1][j1])));
@*/
void histogram(int M,int N,int matrix[M][N],int P,int hist[P]){
  for(int k=0;k<P;k++)
  /*@
    requires Perm(hist[k],write);
    ensures  Perm(hist[k],write);
    ensures  hist[k]==0;
  @*/
  {
    hist[k]=0;
  }

  for(int i=0;i<M;i++){
    for(int j=0;j<N;j++)
      /*@
        loop_invariant M > 0 && N > 0 && P > 0;
        requires (\forall* int k; 0 <= k && k < P ; Reducible(hist[k],+));
        requires Perm(matrix[i][j],1/4);
        requires 0 <= matrix[i][j] && matrix[i][j] < P ;
        ensures  Perm(matrix[i][j],1/4);
        ensures  (\forall* int k; 0 <= k && k < P ; Contribution(hist[k],matrix[i][j]==k?1:0));
      @*/
    {
      hist[matrix[i][j]]+=1;
    }
  }
}

