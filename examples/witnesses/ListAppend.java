// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases ListAppend
//:: tools silicon
//:: options --inline


/**
  This example shows how to use the given keyword to pass
  verification level arguments and also how to use a magic
  wand to prove the iterative implementation of list append
  correct.
  
  The command line to verify with the VerCors Tool is:
  
  vct --silver=silicon --inline ListAppend.java
  
  The expected result is Pass.
*/

class List {

  public int val;
  public List next;
  
  /*@
    public resource state()=
      Perm(val,1)**Perm(next,1)**next->state();

    requires state();
    public pure seq<int> contents()=\unfolding state() \in
        ((next==null)?(seq<int>{val})
                    :(seq<int>{val}+next.contents()));

    public resource list(seq<int> c)=state() ** contents()==c;
  @*/

  /*@
    ensures list(seq<int>{v});
  @*/
  public List(int v){
    val=v;
    next=null;
    //@ fold state();
  }
  
  /*@
    given    seq<int> L1;
    given    seq<int> L2;
    requires this.list(L1);
    requires l!=null ** l.list(L2);
    ensures  this.list(L1+L2);
  @*/
  public void append_rec(List l){
    //@ unfold state();
    if (next==null) {
        next=l;
    } else {
        next.append_rec(l) /*@ with { L1 = next.contents() ; L2 = L2 ; } @*/;
    }
    //@ fold state();
  }

  //@ requires state();
  public /*@ pure @*/ List get_next(){
    //@ unfold state();
    return next;
  }
  
  /*@
    given    seq<int> L1;
    given    seq<int> L2;
    requires this.list(L1);
    requires l!=null ** l.list(L2);
    ensures  this.list(L1+L2);
  @*/
  public void append_iter(List l){
    List cursor=this;
    //@ seq<int> prefix=seq<int>{};
    //@ seq<int> suffix=cursor.contents();
    //@ loop_invariant cursor!=null;
    //@ loop_invariant cursor.state();
    //@ loop_invariant suffix==cursor.contents();
    //@ loop_invariant prefix+suffix==L1;
    //@ loop_invariant l!=null ** l.list(L2);
    //@ loop_invariant wand:(cursor.list(suffix+L2) -* this.list(L1+L2));
    while(cursor.get_next()!=null)
    /*@ with {
        create wand:(this.list(L1+L2) -* this.list(L1+L2)) {}
    } @*/
    {
        //@ List tmp=cursor;
        //@ seq<int> tmp_suffix=suffix;
        //@ unfold cursor.state();
        //@ prefix=prefix+seq<int>{cursor.val};
        //@ suffix=cursor.next.contents();
        cursor=cursor.next;
        /*@
            create wand:(cursor.list(suffix+L2) -* this.list(L1+L2)) {
                use    Perm(tmp.val,1);
                use    Perm(tmp.next,1);
                use    tmp.next==cursor;
                use    tmp_suffix==seq<int>{tmp.val}+suffix;
                fold   tmp.state();
                apply  wand:(tmp.list(tmp_suffix+L2) -* this.list(L1+L2));
            }
        @*/
    }
    //@ unfold cursor.state();
    cursor.next=l;
    //@ fold cursor.state();
    //@ apply wand:(cursor.list(suffix+L2) -* this.list(L1+L2));
  }

}

