package vct.col.util;

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

/**
 * 
 * @author sccblom
 *
 * @param <K>
 * @param <D>
 */
public class NameSpace<K,D> {

  private Stack<Map<K,D>> stack=new Stack<Map<K, D>>();
  
  private Map<K,D> map=new HashMap<K, D>();
 
  public void enter(){
    stack.push(map);
    map=new HashMap<K, D>();
    map.putAll(stack.peek());
  }
  public D lookup(K name){
    return map.get(name);
  }
  public void add(K name,D def){
    map.put(name, def);
  }
  public void leave(){
    map=stack.pop();
  }
}
