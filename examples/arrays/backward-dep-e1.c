// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases backward-dep-err1
//:: tools silicon
//:: verdict Fail

/*@
  invariant  a!=NULL && b !=NULL && c!=NULL;
  invariant \length(a)==len && \length(b)==len && \length(c)==len;
 
  context (\forall* int i ; 0 <= i && i < len ; Perm(a[i],write));
  context (\forall* int i ; 0 <= i && i < len ; Perm(b[i],1/2));
  context (\forall* int i ; 0 <= i && i < len ; Perm(c[i],write));
@*/
void example(int a[],int b[],int c[],int len){  
  for(int i=0;i < len;i++)
   /*@
    requires Perm(a[i],1/2);
    requires i==0 ==> Perm(a[i],1/2);
    requires i < \length(a)-1 ==> Perm(a[i+1],1/2);
    requires Perm(b[i],1/2);
    requires Perm(c[i],write);

    ensures  Perm(a[i],write);      
    ensures  Perm(b[i],1/2);      
    ensures  Perm(c[i],write);          
   @*/
    {
    a[i]=b[i]+1;
    /*@
      S1:if (i>0) {
        recv Perm(a[i],1/2) from S2,1;
      }
    @*/
    S2:if (i < len-1) {
      c[i]=a[i+1]+2;
      //@ send Perm(a[i+1],1/2) to S1,1;
    }
  }
}
