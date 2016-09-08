// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases ForwardDep
//:: tools silicon
//:: verdict Pass

/*@
  invariant a != NULL && b != NULL && c != NULL;
  requires \length(a)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(a[i],write));
  requires \length(b)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(b[i],1/2));
  requires \length(c)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(c[i],write));

  requires (\forall int tid; 0 <= tid && tid < len ; b [ tid ] == tid);

  ensures  \length(a)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(a[i],write));
  ensures  \length(b)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(b[i],1/2));
  ensures  \length(c)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(c[i],write));
  
  ensures  (\forall int i; 0 <= i && i < len ;  a[i] == i+1);
  ensures  (\forall int i; 0 <= i && i < len ;  b[i] == i  );
  ensures  (\forall int i; 0  < i && i < len ;  c[i] == i+2);
@*/
void example(int a[],int b[],int c[],int len){  
  for(int i=0;i < len;i++) /*@
    requires \length(a)==len ** Perm(a[i],write);
    requires \length(b)==len ** Perm(b[i],1/2);
    requires \length(c)==len ** Perm(c[i],write);

    requires b[i]==i;

    ensures  \length(a)==len ** Perm(a[i],1/2);      
    ensures  \length(b)==len ** Perm(b[i],1/2);      
    ensures  \length(c)==len ** Perm(c[i],write);          
    ensures  i>0 ==> Perm(a[i-1],1/2);
    ensures  i==\length(a)-1 ==> Perm(a[i],1/2);
    
    ensures  a[i]==i+1;
    ensures  b[i]==i;
    ensures  i>0 ==> c[i]==i+2;
  @*/ {
    a[i]=b[i]+1;
    /*@
      S1:if (i< len-1) {
        send Perm(a[i],1/2) ** a[i]==i+1 to S2,1;
      }
    @*/
    S2:if (i>0) {
      //@ recv Perm(a[i-1],1/2) ** a[i-1]==i from S1,1;
      c[i]=a[i-1]+2;
    }
  }
}
