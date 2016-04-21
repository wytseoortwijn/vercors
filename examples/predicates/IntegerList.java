// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases IntegerList
//:: tools chalice
//:: verdict Fail

public class IntegerList {

    private int val;
    private IntegerList next;
    //@ int min;

    /*@
        resource state()=
            Perm(val,100)**
            Perm(min,100)**
            Perm(next,100)**
            next->state()**
            next->check_min(min);
        
        requires state();
        pure int get_min()=min;
        
        requires state();
        ensures  \result ==> get_min()==i;
        pure boolean check_min(int i)=min==i;
        
        requires state();
        pure int get_val()=val;
        
        requires state();
        pure IntegerList get_next()=next;
    @*/
    
    /*@
        given int mmin;
        requires mmin <= val ** next->state() ** next->check_min(mmin);
        ensures  state() ** check_min(mmin);
    @*/
    public IntegerList(int val,IntegerList next){
        this.val=val;
        this.next=next;
        //@ this.min=mmin;
        //@ fold state();
    }

    /*@
        requires next !=null ** next.state() ** next.get_min() <= val;
        ensures  \result!=null ** \result.state() ** \result.check_min(\old(next.get_min()));
    @*/
    public static IntegerList cons (int val,IntegerList next){
        /*@
            unfold next.state();
            int tmp=next.min;
            fold next.state();
        @*/
        return  (new IntegerList(val,next) /*@ with { mmin = tmp ; } */);
    }

    /*@
        given int mmin;
        requires mmin <= val;
        ensures  \result!=null ** \result.state() ** \result.check_min(mmin);
    @*/
    public static IntegerList single(int val){
        return  new IntegerList(val,null) /*@ with { mmin=mmin ; } */;
    }

    /* @ spec_ignore @* / public static void main(String args[]){
        main();
    }*/

    static void main(){
        IntegerList list = single(3) /*@ with { mmin = 1 ; } */;
        /* @ spec_ignore @* / System.out.printf("List is %s%n",list);*/
        list = cons(2,list);
        /* @ spec_ignore @* / System.out.printf("List is %s%n",list);*/
        list = cons(1,list);
        /* @ spec_ignore @* / System.out.printf("List is %s%n",list);*/
        list = cons(0,list);
        /* @ spec_ignore @* / System.out.printf("List is %s%n",list);*/
    }

    /* @ spec_ignore @* / public String toString(){
        return toString("[");
    }*/
    /* @ spec_ignore @* / public String toString(String prefix){
        prefix=prefix+val;
        if (next==null) {
            return prefix+"]";
        } else {
            return next.toString(prefix+",");
        }
    }*/
}

