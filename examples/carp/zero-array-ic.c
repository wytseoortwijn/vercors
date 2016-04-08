// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases ZeroArrayIC-C
//:: tools silicon
//:: verdict Pass


/*@
  requires \length(ar)==len ** ArrayPerm(ar,0,1,len,1);
  ensures  \length(ar)==len ** ArrayPerm(ar,0,1,len,1);
  ensures  (\forall int k ; 0 <= k && k < len ; ar[k]==0 );
@*/
void zero_array(int ar[],int len){
    //@ assert \length(ar)==len ;
    for(int i=0;i < len;i++)
       /*@  requires \length(ar)==len ** Perm(ar[i],1);
            ensures  \length(ar)==len ** Perm(ar[i],1) ** ar[i]==0;
       @*/
    {
        ar[i]=0;
    }
}


