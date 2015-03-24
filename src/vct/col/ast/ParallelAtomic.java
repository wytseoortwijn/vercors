package vct.col.ast;

import java.util.ArrayList;

public class ParallelAtomic extends ASTNode {

  @Override
  public <R,A> R accept_simple(ASTMapping1<R,A> map,A arg){
    return map.map(this,arg);
  }

  
  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    try {
      visitor.visit(this);
    } catch (Throwable t){
      if (thrown.get()!=t){
        System.err.printf("Triggered by %s:%n",getOrigin());
        thrown.set(t);
     }
      throw t;
    }
  }
  
  @Override
  public <T> T accept_simple(ASTMapping<T> map){
    try {
      return map.map(this);
    } catch (Throwable t){
      if (thrown.get()!=t){
        System.err.printf("Triggered by %s:%n",getOrigin());
        thrown.set(t);
    }
      throw t;
    }
  }
 
 
  public final BlockStatement block; 
  
  public final ArrayList<String> sync_list;
  
  
  public ParallelAtomic(BlockStatement block,String ... sync){
    sync_list=new ArrayList();
    for(String s:sync){
      sync_list.add(s);
    }
    this.block=block;
  }

}
