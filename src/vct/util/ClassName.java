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

  public String toString(String separator) {
    StringBuilder builder=new StringBuilder();
    builder.append(name[0]);
    for(int i=1;i<name.length;i++){
      builder.append(separator);
      builder.append(name[i]);
    }
    return builder.toString();
  }
  
  public static String[] copy(String name[]){
    return Arrays.copyOf(name,name.length);
  }
  
  public static boolean prefixOf(String name1[],String name2[]){
    int N=name1.length;
    if (name2.length!=N) return false;
    N--;
    for (int i=0;i<N;i++){
      if (!name1[i].equals(name2[i])) return false;
    }
    return name2[N].startsWith(name1[N]);
  }

}
