// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases SummationReduction
//:: suite puptol
//:: tools silicon
//:: verdict Pass

float res;

/*@
  given seq<float> as;
  invariant ar!=NULL;
  invariant N>0;
  context Perm(res,write);
  context (\forall* int k ; 0 <= k && k < N ; PointsTo(ar[k],1/2,as[k]));
  ensures  res==(\sum int k ; 0 <= k && k < N ; as[k] );
@*/
void do_sum(int N,float ar[N]){
  res=(float)0;
  for(int i=0;i<N;i++)
    /*@
      requires Reducible(res,+);
      context  PointsTo(ar[i],1/4,as[i]);
      ensures  Contribution(res,as[i]);
    */
  {
    res+=ar[i];
  }
}

