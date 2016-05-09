// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases TreeStack
//:: tools chalice
//:: suite medium

/*
    Note that this specification only validates access permissions.
    TODO:
      * extend state with all properties of a binary search tree.
     
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
    requires t!=null ** t.state();
    ensures  \result->state();
  @*/
  public Tree del_min(Tree t){
        //@ unfold t.state();
	    Tree tt, pp, p;
	    p = t.left;
        Stack stk;
	   if (p == null) {
	       tt = t.right;
           return tt;
	   } else {
           //@ unfold p.state();
	       pp = t;
           tt = p.left;
           stk = null;
           //@ loop_invariant pp!=null;
           //@ loop_invariant p!=null;
           //@ loop_invariant Perm(p.left,100)**Perm(p.right,100);
           //@ loop_invariant Perm(p.data,100)**p.right->state();
           //@ loop_invariant Perm(pp.left,100)**Perm(pp.right,100);
           //@ loop_invariant Perm(pp.data,100)**pp.right->state();
           //@ loop_invariant p==pp.left;
           //@ loop_invariant tt==p.left;
           //@ loop_invariant tt->state();
           //@ loop_invariant stk->state();
           //@ loop_invariant stk==null ==> pp==t;
           //@ loop_invariant stk!=null ==> stk.get_root()==t;
           //@ loop_invariant stk!=null ==> stk.get_ref_left()==pp ;
	       while (tt != null) {
                stk=new Stack(pp,stk,t);
                //@ unfold tt.state();
		        pp = p;
                p = tt;
                tt = p.left;
	       }
	       tt = p.right;
           pp.left= tt;
           /*@
               fold pp.state();
               loop_invariant pp!= null ** pp.state();
               loop_invariant stk->state();
               loop_invariant stk!=null ==> stk.get_ref_left() == pp ;
               loop_invariant stk==null ==> pp==t;
               loop_invariant stk!=null ==> stk.get_root()==t;
               while(stk!=null){
                 unfold stk.state();
                 pp = stk.ref;
                 stk = stk.tail;
                 fold pp.state();
               }
           */
           return t;
	   }
	 }
}

class Stack {
  public Tree root;
  public Tree ref;
  public Stack tail;
  
  /*@
    public resource state()=
        Perm(ref,100)**Perm(tail,100)**Perm(root,100)**tail->state()**ref!=null **
        Perm(ref.data,100)**Perm(ref.left,100)**Perm(ref.right,100)**ref.right->state()
        ** ((tail!=null)==>(ref==tail.get_ref_left() ** root==tail.get_root()))
        ** (tail==null ==> ref==root);
        
  @*/
  /*@
    requires ref!=null ** tail->state();
    requires Perm(ref.data,100)**Perm(ref.left,100)**Perm(ref.right,100)**ref.right->state();
    requires tail!=null ==> ref==tail.get_ref_left();
    requires tail!=null ==> root==tail.get_root();
    requires tail==null ==> ref==root;
    ensures  state() ** get_root()==root ** get_ref_left()==\old(ref.left);
  @*/
  public Stack(Tree ref,Stack tail,Tree root){
    this.ref=ref;
    this.tail=tail;
    this.root=root;
    //@ fold this.state();
  }

  /*@
    requires state();
    public pure Tree get_ref()=ref; 
   @*/

  /*@
    requires state();
    public pure Tree get_ref_left()=ref.left; 
   @*/

  /*@
    requires state();
    public pure Tree get_root()=root;
   @*/
}


