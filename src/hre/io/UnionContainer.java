package hre.io;

import java.io.IOException;
import java.io.InputStream;

public class UnionContainer implements Container {

  private Container path[];
  
  public UnionContainer(Container ... path){
    this.path=path;
  }

  @Override
  public boolean contains(String name) {
    for(int i=0;i<path.length;i++){
      if (path[i].contains(name)) return true;
    }
    return false;
  }
  
  @Override
  public InputStream read(String name) throws IOException {
    for(int i=0;i<path.length;i++){
      if (path[i].contains(name)) return path[i].read(name);
    }
    return null;
  }
  
  @Override
  public long size(String name) {
    for(int i=0;i<path.length;i++){
      if (path[i].contains(name)) return path[i].size(name);
    }
    return 0;
  }
     
}
