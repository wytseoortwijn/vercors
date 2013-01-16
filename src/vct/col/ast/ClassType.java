package vct.col.ast;

import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Warning;

import java.util.Arrays;

public class ClassType extends Type {

  private final String name[];
  private final ASTNode args[];
  
  public ClassType(String name[],ASTNode ... args){
    this.name=Arrays.copyOf(name,name.length);
    this.args=Arrays.copyOf(args,args.length);
  }
  
  public ASTNode[] getArgs(){
    return args;
  }
  
  public ASTNode getArg(int i){
    return args[i];
  }


  public String[] getNameFull(){
    return Arrays.copyOf(name,name.length);
  }
  
  public ClassType(String name) {
    this.name=new String[1];
    this.name[0]=name;
    args=null;
  }
  public ClassType(String name[]) {
    if (name.length==0) Abort("illegal name of length 0");
    this.name=Arrays.copyOf(name,name.length);
    args=null;
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

  public boolean supertypeof(ProgramUnit context, Type t){
    if (t instanceof ClassType) {
      ClassType ct=(ClassType)t;
      // java.lang.Object is supertype of everything.
      if (name.length==3 && name[0].equals("java") &&
          name[1].equals("lang") && name[2].equals("Object")) return true;
      // Everything is a supertype of <<null>>.
      if (ct.name.length==1 && ct.name[0].equals("<<null>>")) return true;
      if (ct.name.length==1 && ct.name[0].equals("<<label>>")) return true;
      return supertype_search(context,ct);
    }
    return false;
  }
  
  
  private boolean supertype_search(ProgramUnit context, ClassType ct) {
    Debug("checking if %s is asuper type of %s",this,ct);
    if (ct.name.length==name.length){
      int i=0;
      while(i<name.length){
        if (!ct.name[i].equals(name[i])) break;
        i++;
      }
      if (i==name.length) return true;
    }
    Debug("argument is not the same type not the same type");
    if (context==null) {
      Debug("missing context");
      return false;
    }
    ASTClass cl=context.find(ct);
    if (cl==null) {
      Debug("class not found");
      return false;
    }
    for(ClassType ct_parent:cl.super_classes){
      if (supertype_search(context,ct_parent)) return true;
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
  public ASTNode zero(){
    return new NameExpression(NameExpression.Kind.Reserved,"null");
  }
  
  public boolean isNull(){
    return name.length==1 && name[0].equals("<<null>>"); 
  }
}
