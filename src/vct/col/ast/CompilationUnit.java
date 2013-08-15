package vct.col.ast;

import java.util.ArrayList;
import java.util.Iterator;

import vct.util.ClassName;

public class CompilationUnit implements ASTSequence<CompilationUnit> {

  private ProgramUnit parent;
  
  public void attach(ProgramUnit parent){
    this.parent=parent;
    for(ASTNode item:contents){
      if (parent!=null && item instanceof ASTDeclaration){
        ((ASTDeclaration)item).attach(parent,null);
      }      
    }
  }
  
  private String name;
  
  private ArrayList<ASTNode> contents=new ArrayList<ASTNode>();
  
  public CompilationUnit(String name){
    this.name=name;
  }
  
  public String getFileName(){
    return name;
  }
  
  public CompilationUnit add(ASTNode item){
    if (parent!=null && item instanceof ASTDeclaration){
      ((ASTDeclaration)item).attach(parent,null);
      if (item instanceof ASTClass){
        ASTClass cl=(ASTClass)item;
        parent.classes.put(cl.getDeclName(),cl);
      }

    }
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
