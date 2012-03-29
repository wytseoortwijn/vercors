package vct.util;

import java.util.Arrays;

public class ClassName {

  public final String name[];
  
  public ClassName(String name[]){
    this.name=Arrays.copyOf(name,name.length);
  }
  
  public static boolean equal(String name1[],String name2[]){
    if (name1.length!=name2.length) return false;
    for(int i=0;i<name1.length;i++){
      if (!name1[i].equals(name2[i])) return false;
    }
    return true;
  }
  
}
