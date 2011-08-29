package vct.col.util;

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

public class NameSpace {

  private Stack<Map<String,AnyDefinition>> stack=new Stack();
  
  private Map<String,AnyDefinition> map=new HashMap();
 
  public void enter(){
    stack.push(map);
    map=new HashMap();
    map.putAll(stack.peek());
  }
  public AnyDefinition lookup(String name){
    return map.get(name);
  }
  public void add(String name,AnyDefinition def){
    map.put(name, def);
  }
  public void leave(){
    map=stack.pop();
  }
}
