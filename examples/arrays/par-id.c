// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases par-id-c
//:: tools silicon
//:: verdict Pass
/*@
  invariant a != NULL;
  requires \length(a)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(a[i],write));
  ensures  \length(a)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(a[i],write));
  ensures  (\forall int i ; 0 <= i && i < len ; a[i]==\old(a[i]));
@*/
void example(int a[],int len){  
  for(int i=0;i < len;i++)
   /*@
    requires \length(a)==len ** Perm(a[i],write);
    ensures  \length(a)==len ** Perm(a[i],write);
    ensures  a[i]==\old(a[i]);
   @*/
    {
      a[i]=a[i];
    }
    if (len >0){
     //@ assert Perm(a[0],write);
     //@ assert a[0]==\old(a[0]);
    }
    {
      //@ assert (\forall int i ; 0 <= i && i < len ; a[i]==\old(a[i]));
    }
}
