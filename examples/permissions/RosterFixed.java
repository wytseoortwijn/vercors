// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases RosterFixed
//:: tools chalice

/* See pg 42, phd Hurlin. */

class Roster {
  int id;
  int grade;
  Roster next;

/*@
  resource ids_and_links()=Perm(id,100) ** Perm(next,50) ** next->ids_and_links();
 
  resource grades_and_links()=Perm(grade,100) ** Perm(next,50) ** next->grades_and_links() ;

  resource state()= ids_and_links() ** grades_and_links();
 */
 
  //@ requires n->state();
  //@ ensures  this.state();
  Roster(int i, int g, Roster n) {
    id = i;
    grade = g;
    next = n;
    /*@
      if (n!=null) { unfold n.state(); }
    */
    //@ fold ids_and_links();
    //@ fold grades_and_links();
    //@ fold state();
  }

  //@ requires state();
  //@ ensures  state();
  void updateGrade(int id, int grade) {
    /*@
      unfold state();
      unfold ids_and_links();
      unfold grades_and_links();
    @*/
    if (this.id == id) {
      this.grade = grade;
    } else if (next != null) {
      //@ fold next.state();
      next.updateGrade(id,grade);
      //@ unfold next.state();
    }
    /*@
      fold ids_and_links();
      fold grades_and_links();
      fold state();
    @*/
  }

  //@ requires ids_and_links();
  //@ ensures  ids_and_links();
  boolean contains(int id) {
    //@ unfold ids_and_links();
    boolean b = this.id==id;
    if(!b && next!=null){
      b=next.contains(id);
    }
    //@ fold ids_and_links();
    return b;
  }
}

