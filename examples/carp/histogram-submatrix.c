// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases HistogramSubMatrix
//:: tools silicon
//:: verdict Pass

/*
  vct --silver=silicon_qp histogram-submatrix.c
*/

/*@
  given seq<seq<int> > data;
  given frac p;
  invariant p!=none && M>0 && N > 0 && P > 0 && step >= N && \matrix(matrix,M,N) && \array(hist,P);

  context (\forall* int i1 ; 0 <= i1 && i1 < M ;
             (\forall* int j1 ; 0 <= j1 && j1 < N ;
               Perm(matrix[i1][j1],p)));
  context (\forall int i1 ; 0 <= i1 && i1 < M ;
             (\forall int j1 ; 0 <= j1 && j1 < N ;
               0 <= matrix[i1][j1] && matrix[i1][j1] < P));
  context (\forall int i1 ; 0 <= i1 && i1 < M ;
             (\forall int j1 ; 0 <= j1 && j1 < N ;
               matrix[i1][j1] == data[i1][j1] ));
  context (\forall* int i1 ; 0 <= i1 && i1 < P ;
               Perm(hist[i1],write));
  ensures  (\forall int k; 0 <= k && k < P ; hist[k]==
               (\sum int i1 ; 0 <= i1 && i1 < M ;
                 (\sum int j1 ; 0 <= j1 && j1 < N ;
                   data[i1][j1]==k?1:0)));
@*/
void histogram(int M,int N,int step,int matrix[M][step],int P,int hist[P]){
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
        requires (\forall* int k; 0 <= k && k < P ; Reducible(hist[k],+));
        context  Perm(matrix[i][j],p);
        context  0 <= matrix[i][j] ** matrix[i][j] < P ; // can be proven.
        //context 0 <= matrix[i][j] && matrix[i][j] < P ; // equivalent but cannot be proven.
        context  matrix[i][j]==data[i][j];
        ensures  (\forall* int k; 0 <= k && k < P ; Contribution(hist[k],data[i][j]==k?1:0));
      @*/
    {
      hist[matrix[i][j]]+=1;
    }
  }
}

