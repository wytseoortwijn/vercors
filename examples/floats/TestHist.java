// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases TestHist
//:: tools silicon
//:: verdict Pass

class Testhist {
  
  /*@
    given seq<seq<boolean>> vals;
    invariant a != null && hist != null;
    invariant (\forall* int i; 0 <= i && i < a.length ; Perm(a[i],1/2));
    invariant (\forall* int i; 0 <= i && i < hist.length ; Perm(hist[i],1));
    invariant (\forall int i; 0 <= i && i < a.length ; 0 <= a[i] && a[i] < hist.length);
    //invariant |vals|==hist.length && (\forall int i; 0 <= i && i < hist.length ; |vals[i]|==a.length);
    invariant (\forall int i; 0 <= i && i < hist.length ; 
                (\forall int j ; 0 <= j && j < a.length ; (vals[i])[j] == (i==a[j])));
    ensures   (\forall int i; 0 <= i && i < hist.length ; hist[i]==\count(vals[i],0,a.length));
  @*/
  public void histogram(int a[],int hist[]){
    int k=0;
    //@ loop_invariant 0 <= k && k <= hist.length;
    //@ loop_invariant (\forall int i; 0 <= i && i < k ; hist[i]==\count(vals[i],0,0));
    while(k<hist.length){
      hist[k]=0;
      k++;
    }
    k=0;
    //@ loop_invariant 0 <= k && k <= a.length;
    //@ loop_invariant (\forall int i; 0 <= i && i < hist.length ; hist[i]==\count(vals[i],0,k));
    while(k<a.length){
      int v=a[k];
      hist[v]++;
      k++;
      assert hist[v]==\count(vals[v],0,k);
      assert (\forall int i; 0 <= i && i < hist.length ; i != v ==> \count(vals[i],0,k-1)==\count(vals[i],0,k));
      assert (\forall int i; 0 <= i && i < hist.length ; i != v ==> hist[i]==\count(vals[i],0,k));
    }
  }
  
}

