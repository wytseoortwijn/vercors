// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases forward-dep-err1
//:: tools silicon
//:: verdict Fail

/*@
  requires \length(a)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(a[i],write));
  requires \length(b)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(b[i],1/2));
  requires \length(c)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(c[i],write));

  ensures  \length(a)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(a[i],write));
  ensures  \length(b)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(b[i],1/2));
  ensures  \length(c)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(c[i],write));
  @*/

void example(int a[],int b[],int c[],int len){  
  //@ assert \length(a)==len;
  //@ assert \length(b)==len;
  //@ assert \length(c)==len;
  for(int i=0;i < len;i++)
   /*@
    requires \length(a)==len ** Perm(a[i],write);
    requires \length(b)==len ** Perm(b[i],1/2);
    requires \length(c)==len ** Perm(c[i],write);

    ensures  \length(a)==len ** Perm(a[i],1/2);      
    ensures  \length(b)==len ** Perm(b[i],1/2);      
    ensures  \length(c)==len ** Perm(c[i],write);          

    ensures i>0 ==> Perm(a[i-1],1/2);
    ensures i==\length(a)-1 ==> Perm(a[i],1/2);
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
