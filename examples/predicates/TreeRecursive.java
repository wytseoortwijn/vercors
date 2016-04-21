// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases TreeRecursive
//:: tools chalice
/**
  
  The command line to verify with the VerCors Tool is:
  
  vct --chalice TreeRecursive.java
  
  The expected result is Pass.
*/

public class Tree {

  public int data;
  public Tree left;
  public Tree right;

  /*@
    public resource state()=Perm(data,100)**
	Perm(left,100)**Perm(right,100)**
	left->state()**right->state();
  @*/

  /*@
    requires t->state();
    ensures  t!=null ==> \result.length > 0;
    public pure seq<int> contents(Tree t){
      if(t==null){
          return seq<int>{};
      } else {
          unfold t.state();
          return contents(t.left)+seq<int>{t.data}+contents(t.right);
      }
    }
  */
  
  /*@
    requires t!=null ** t.state();
    ensures  \result->state();
    ensures  contents(\result)==tail(\old(contents(t)));
  @*/
  public Tree del_min(Tree t){
    //@ unfold t.state();
    if (t.left==null) {
      //@ assert contents(t.left) == seq<int>{};
      return t.right;
    } else {
      t.left=del_min(t.left);
      //@ fold t.state();
      return t;
    }
  }
}

