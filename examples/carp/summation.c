// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases Summation
//:: tools silicon
//:: verdict Pass

int res;

/*@
  invariant ar!=NULL;
  requires N>0;
  requires Perm(res,write);
  requires (\forall* int k ; 0 <= k && k < N ; Perm(ar[k],1/2));
  ensures  N>0;
  ensures  Perm(res,write);
  ensures  (\forall* int k ; 0 <= k && k < N ; Perm(ar[k],1/2));
  ensures  (\forall int k ; 0 <= k && k < N ; ar[k]==\old(ar[k]));
  ensures  res==(\sum int k ; 0 <= k && k < N ; ar[k] );
@*/
void do_sum(int N,int ar[N]){
  res=0;
  for(int i=0;i<N;i++)
    /*@
      loop_invariant N>0;
      requires Reducible(res,+);
      requires Perm(ar[i],1/4);
      ensures  Perm(ar[i],1/4);
      ensures  Contribution(res,ar[i]);
    */
  {
    res+=ar[i];
  }
}

