package vct.col.ast;

public class ClassType extends Type {

  public final String name[];
  public ClassType(String name) {
    this.name=new String[1];
    this.name[0]=name;
  }
  public ClassType(String name[]) {
    this.name=name;
  }
  public String getName(){
    return name[name.length-1];
  }
  public String getFullName(){
    String res=name[0];
    for(int i=1;i<name.length;i++){
      res+="."+name[i];
    }
    return res;
  }

  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }

  public boolean supertypeof(Type t){
    if (t instanceof ClassType) {
      ClassType ct=(ClassType)t;
      // catch universal type
      if (ct.name.length==0) return true;
      if (ct.name.length==name.length){
        int i=0;
        while(i<name.length){
          if (!ct.name[i].equals(name[i])) break;
          i++;
        }
        if (i==name.length) return true;
      }
      // TODO: check inheritance.
    }
    return false;
  }
  
  public String toString(){
    return getFullName();
  }
  
}
