package hre.util;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Stack;

public class NameSpace <Key,Data> implements FrameControl {

  private final class List {
    final Data item;
    final List next;
    public List(Data item,List next){
      this.item=item;
      this.next=next;
    }
  }
  private Stack<Map<Key,List>> stack=new Stack<Map<Key,List>>();
  private Map<Key,List> map=new HashMap<Key,List>();
  
  private final class KeyIterator implements Iterator<Data> {
    Key k;
    List list;
    int next;
    KeyIterator(Key k){
      this.k=k;
      next=stack.size()-1;
    }
    public boolean hasNext(){
      for(;;){
        if (list!=null) return true;
        if (next<0) return false;
        list=stack.get(next).get(k);
        next--;
      }
    }
    public Data next(){
      Data res=list.item;
      list=list.next;
      return res;
    }
    public void remove(){
      throw new UnsupportedOperationException();
    }
  }
 
  public void enter(){
    stack.push(map);
    map=new HashMap<Key,List>();
  }
  
  public Iterator<Data> lookup(Key k){
    return new KeyIterator(k);
  }
  public void add(Key k,Data d){
    List l=map.get(k);
    l=new List(d,l);
    map.put(k, l);
  }
  public void leave(){
    map=stack.pop();
  }
}
