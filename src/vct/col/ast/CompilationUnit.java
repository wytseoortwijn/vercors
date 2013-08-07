package vct.col.ast;

import java.util.ArrayList;
import java.util.Iterator;

public class CompilationUnit implements ASTSequence<CompilationUnit> {

  private String name;
  
  private ArrayList<ASTNode> contents=new ArrayList<ASTNode>();
  
  public CompilationUnit(String name){
    this.name=name;
  }
  
  public String getFileName(){
    return name;
  }
  
  public CompilationUnit add(ASTNode item){
    contents.add(item);
    return this;
  }
  
  public int size(){
    return contents.size();
  }
  
  public ASTNode get(int i){
    return contents.get(i);
  }
  
  public Iterable<ASTNode> get(){
    return contents;
  }
  
  public <T> void accept(ASTVisitor<T> visitor) {
    for(ASTNode n:contents){
      n.accept(visitor);
    }
  }

  @Override
  public Iterator<ASTNode> iterator() {
    return contents.iterator();
  }

}
