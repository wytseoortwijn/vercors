// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases forward-dep-err1
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
    requires Perm(a[i],write);
    ensures  Perm(a[i],1/2);      
    ensures  i>0 ==> Perm(a[i-1],1/2);
    ensures  i==\length(a)-1 ==> Perm(a[i],1/2);
    
    context  Perm(b[i],1/2);      
    context  Perm(c[i],write);          
   @*/
    {
    
    a[i]=b[i]+1;
    S1:if (i< len-1) {
      //@ send Perm(a[i],1/2) to S2,1;
    }
    S2:if (i>0) {
      //@ recv Perm(a[i-1],1/2) from S1,1;
      c[i]=a[i+1]+2;
    }
  }
}
