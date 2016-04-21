// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases zero-matrix-c
//:: tools silicon

/*@
  requires M>0 && N > 0 ;
  requires (\forall* int i1 ; 0 <= i1 && i1 < M ;
             (\forall* int j1 ; 0 <= j1 && j1 < N ;
               Perm(matrix[i1][j1],write)));
  ensures  (\forall* int i2 ; 0 <= i2 && i2 < M ;
             (\forall* int j2 ; 0 <= j2 && j2 < N ;
               Perm(matrix[i2][j2],write)));
  ensures  (\forall int i3 ; 0 <= i3 && i3 < M ;
             (\forall int j3 ; 0 <= j3 && j3 < N ;
               matrix[i3][j3]==0));
@*/
void zero(int M,int N,int matrix[M][N]){
  for(int i=0;i<M;i++){
    for(int j=0;j<N;j++)
      /*@
        requires Perm(matrix[i][j],write);
        ensures  Perm(matrix[i][j],write);
        ensures  matrix[i][j]==0;
      @*/
    {
      matrix[i][j]=0;
      //@ assert M * N > 0;
    }
  }
}

