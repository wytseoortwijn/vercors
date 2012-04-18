package vct.col.ast;

import static hre.System.Abort;

public class ClassType extends Type {

  public final String name[];
  public ClassType(String name) {
    this.name=new String[1];
    this.name[0]=name;
  }
  public ClassType(String name[]) {
    if (name.length==0) Abort("illegal name of length 0");
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
      // java.lang.Object is supertype of everything.
      if (name.length==3 && name[0].equals("java") &&
          name[1].equals("lang") && name[2].equals("Object")) return true;
      // Everything is a supertype of <<null>>.
      if (ct.name.length==1 && ct.name[0].equals("<<null>>")) return true;
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
  
  public int hashCode(){
    return getFullName().hashCode();
  }
  public boolean equals(Object o){
    if (o instanceof ClassType) {
      return getFullName().equals(((ClassType)o).getFullName());
    } else {
      return false;
    }
  }
  
}
