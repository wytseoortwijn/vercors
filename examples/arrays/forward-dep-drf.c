// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases forward-dep-drf
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
  for(int i=0;i < N;i++) /*@
    requires Perm(a[i],write) ** Perm(b[i],1/2) ** Perm(c[i],write);
    ensures  Perm(a[i],1/2) ** Perm(b[i],1/2) ** Perm(c[i],write);          
    ensures  (i>0 ==> Perm(a[i-1],1/2)) ** (i==N-1 ==> Perm(a[i],1/2));
  @*/ {
    a[i]=b[i]+1;
    /*@
      S1:if (i< N-1) {
        send Perm(a[i],1/2) to S2,1;
      }
    @*/
    S2:if (i>0) {
      //@ recv Perm(a[i-1],1/2) from S1,1;
      c[i]=a[i-1]+2;
    }
  }
}
