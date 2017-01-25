// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases AccessSubMatrix
//:: tools silicon
//:: pass Ref.good1
//:: fail Ref.bad1 Ref.bad2

/*@
  requires matrix != NULL;
  requires M>0 && N > 0 && step > N ;
  requires (\forall* int i1 ; 0 <= i1 && i1 < M ;
             (\forall* int j1 ; 0 <= j1 && j1 < N ;
               Perm(matrix[i1][j1],write)));
@*/
void good1(int M,int N,int step,int matrix[M][step]){
  matrix[0][0]=0;
}

/*@
  requires matrix != NULL;
  requires M>0 && N > 0 && step > N ;
  requires (\forall* int i1 ; 0 <= i1 && i1 < M ;
             (\forall* int j1 ; 0 <= j1 && j1 < N ;
               Perm(matrix[i1][j1],write)));
@*/
void bad1(int M,int N,int step,int matrix[M][step]){
  matrix[0][N]=0;
}

/*@
  requires M>0 && N > 0 && step > N ;
  requires (\forall* int i1 ; 0 <= i1 && i1 < M ;
             (\forall* int j1 ; 0 <= j1 && j1 < N ;
               Perm(matrix[i1][j1],write)));
@*/
void bad2(int M,int N,int step,int matrix[M][step]){
  matrix[0][0]=0;
}

