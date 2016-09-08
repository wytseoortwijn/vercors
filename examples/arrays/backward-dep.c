// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases backward-dep
//:: tools silicon

/*@
  invariant  a!=NULL && b !=NULL && c!=NULL;
  invariant \length(a)==len && \length(b)==len && \length(c)==len;
  
  requires (\forall* int i ; 0 <= i && i < len ; Perm(a[i],write));
  requires (\forall* int i ; 0 <= i && i < len ; Perm(b[i],1/2));
  requires (\forall* int i ; 0 <= i && i < len ; Perm(c[i],write));

  requires (\forall int tid; 0 <= tid && tid < len ; a [ tid ] == 0);
  requires (\forall int tid; 0 <= tid && tid < len ; b [ tid ] == tid);

  ensures  (\forall* int i ; 0 <= i && i < len ; Perm(a[i],write));
  ensures  (\forall* int i ; 0 <= i && i < len ; Perm(b[i],1/2));
  ensures  (\forall* int i ; 0 <= i && i < len ; Perm(c[i],write));
  
  ensures  (\forall int i; 0 <= i && i < len ;  a[i] == i+1);
  ensures  (\forall int i; 0 <= i && i < len ;  b[i] == i  );
  ensures  (\forall int i; 0 <= i && i < len-1 ;  c[i] == 2  );
@*/
void example(int a[],int b[],int c[],int len){  
  for(int i=0;i < len;i++)
   /*@
    requires Perm(a[i],1/2);
    requires i==0 ==> Perm(a[i],1/2);
    requires i < len-1 ==> Perm(a[i+1],1/2);
    requires Perm(b[i],1/2);
    requires Perm(c[i],write);
    requires i < len-1 ==> a[i+1]==0;
    requires b[i]==i;

    ensures  Perm(a[i],write);      
    ensures  Perm(b[i],1/2);      
    ensures  Perm(c[i],write);          
    ensures  a[i]==i+1;
    ensures  b[i]==i;
    ensures  i < len-1 ==> c[i]==2;
   @*/
    {
    /*@
      S1:if (i>0) {
        recv i == (i-1)+1 ** \length(a)==len ** Perm(a[i],1/2) from S2,1;
      }
    @*/
    a[i]=b[i]+1;
    S2:if (i < len-1) {
      c[i]=a[i+1]+2;
      //@ send \length(a)==len ** Perm(a[i+1],1/2) to S1,1;
    }
  }
}

