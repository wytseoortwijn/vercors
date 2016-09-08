// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases indep-loop-drf
//:: tools silicon
//:: verdict Pass
/*@
  invariant  a!=NULL && b !=NULL && c!=NULL;
  invariant \length(a)==N && \length(b)==N && \length(c)==N;

  requires \length(a)==N ** (\forall* int i ; 0 <= i && i < N ; Perm(a[i],write));
  requires \length(c)==N ** (\forall* int i ; 0 <= i && i < N ; Perm(c[i],write));
  requires \length(b)==N ** (\forall* int i ; 0 <= i && i < N ; Perm(b[i],1/2));

  ensures  \length(a)==N ** (\forall* int i ; 0 <= i && i < N ; Perm(a[i],write));
  ensures  \length(c)==N ** (\forall* int i ; 0 <= i && i < N ; Perm(c[i],write));
  ensures  \length(b)==N ** (\forall* int i ; 0 <= i && i < N ; Perm(b[i],1/2));
@*/
void example(int a[],int b[],int c[],int N){  
  for(int i=0;i<N;i++) /*@
    requires Perm(a[i],write) ** Perm(c[i],write) ** Perm(b[i],1/2);
    ensures  Perm(a[i],write) ** Perm(c[i],write) ** Perm(b[i],1/2);
  @*/ {
    a[i] = b[i] + 1;  
    c[i] = a[i] + 2;
  }
}
