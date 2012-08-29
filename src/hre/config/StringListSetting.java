package hre.config;

import java.util.ArrayList;
import java.util.Iterator;

public class StringListSetting implements Iterable<String> {

  private ArrayList<String> list=new ArrayList<String>();
  
  public Option getAppendOption(String help){
    return new AppendOption(help);
  }
  @Override
  public Iterator<String> iterator() {
    return list.iterator();
  }
  
  private class AppendOption extends AbstractOption{
    public AppendOption(String help){
      super(true,help);
    }
    public void pass(String arg){
      for(String item:arg.split(",")){
        list.add(item);
      }
    }
  }

  public boolean contains(String item) {
    return list.contains(item);
  }
}
