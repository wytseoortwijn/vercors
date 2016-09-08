// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases zero-array-c
//:: tools silicon
//:: verdict Pass


/*@
  invariant ar!=NULL && \length(ar)==len;
  requires (\forall* int i;0<=i && i < len;Perm(ar[i],write));
  ensures  (\forall* int i;0<=i && i < len;Perm(ar[i],write));
  ensures  (\forall int k ; 0 <= k && k < len ; ar[k]==0 );
@*/
void zero_array(int ar[],int len){
    //@ assert \length(ar)==len ;
    for(int i=0;i < len;i++)
       /*@  requires Perm(ar[i],write);
            ensures  Perm(ar[i],write) ** ar[i]==0;
       @*/
    {
        ar[i]=0;
    }
}


