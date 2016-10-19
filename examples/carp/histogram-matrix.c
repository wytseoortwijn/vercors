// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases HistogramMatrix
//:: suite puptol
//:: tools silicon
//:: verdict Pass

//begin(all)
/*@
  invariant M>0 && N > 0 && P > 0;
  invariant \matrix(matrix,M,N) ** \array(hist,P);
  context (\forall* int i1 ; 0 <= i1 && i1 < M ; 
            (\forall* int j1 ; 0 <= j1 && j1 < N ;
              Perm(matrix[i1][j1],1/2)));
  context (\forall int i1 ; 0 <= i1 && i1 < M ;
            (\forall int j1 ; 0 <= j1 && j1 < N ;
              0 <= matrix[i1][j1] && matrix[i1][j1] < P));
  context (\forall* int i1 ; 0 <= i1 && i1 < P ;
            Perm(hist[i1],write));            
  ensures (\forall int k; 0 <= k && k < P ; hist[k]==
            (\sum int i1 ; 0 <= i1 && i1 < M ;
              (\sum int j1 ; 0 <= j1 && j1 < N ;
                matrix[i1][j1]==k?1:0)));
  ensures (\forall int i1 ; 0 <= i1 && i1 < M ;
            (\forall int j1 ; 0 <= j1 && j1 < N ;
              matrix[i1][j1]==\old(matrix[i1][j1])));
@*/
void histogram(int M,int N,int matrix[M][N],int P,int hist[P]){
  for(int k=0;k<P;k++)
  /*@
    context Perm(hist[k],write);
    ensures hist[k]==0;
  @*/
  {
    hist[k]=0;
  }

  for(int i=0;i<M;i++){
    for(int j=0;j<N;j++)
      /*@
        requires (\forall* int k; 0 <= k && k < P ; Reducible(hist[k],+)); $\label{histogram reducible}$
        context  Perm(matrix[i][j],1/4);
        context  0 <= matrix[i][j] && matrix[i][j] < P ;
        ensures  (\forall* int k; 0 <= k && k < P ; Contribution(hist[k],matrix[i][j]==k?1:0));
      @*/
    {
      hist[matrix[i][j]]+=1;
    }
  }
}
//end(all)

