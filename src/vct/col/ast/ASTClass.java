// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.ast.MessageOrigin;
import hre.util.FilteredIterable;

import java.util.*;

import vct.col.util.DeclarationFilter;
import vct.col.util.MethodFilter;

import static hre.System.Abort;
import static hre.System.Debug;

/** This class is the main container for declarations.
 *  For Java it contains both classes and packages.
 *  For PVL it contain both classes and the top level class list
 *  and block.
 * @author sccblom
 *
 */
public class ASTClass extends ASTNode {
  /**
   * Enumeration of the kinds of classes that are considered.
   * 
   * @author sccblom
   */
  public static enum ClassKind {
    Package,
    Interface,
    Abstract,
    Plain
  };
  
  /** contains the kind of class. */
  public final ClassKind kind;
  /** contains the name of the class/module/package. */
  public final String name;
  /** contains the parent of this unit */
  private ASTClass parent_class;
  /** contains the static entries */
  private ArrayList<ASTNode> static_entries=new ArrayList<ASTNode>();
  /** contains the dynamic entries. */
  private ArrayList<ASTNode> dynamic_entries=new ArrayList<ASTNode>();

  
  private void getFullName(ArrayList<String> fullname){
    if (parent_class!=null) parent_class.getFullName(fullname);
    if (name!=null) fullname.add(name); 
  }
  public String[] getFullName(){
    ArrayList<String> fullname=new ArrayList();
    getFullName(fullname);
    return fullname.toArray(new String[0]);
  }

  /** Create an empty root class. */
  public ASTClass(){
    kind=ClassKind.Package;
    name=null;
  }
  /** Create a root class from a given block statement. */
  public ASTClass(BlockStatement node) {
    kind=ClassKind.Package;
    name=null;
    int N=node.getLength();
    for(int i=0;i<N;i++){
      static_entries.add(node.getStatement(i));
    }
  }

  /** Create a new class in a hierarchy. */
  public ASTClass(String name,ASTClass parent,boolean is_static,ClassKind kind){
    this.kind=kind;
    this.name=name;
    this.parent_class=parent;
    if(is_static){
      parent.add_static(this);
    } else {
      parent.add_dynamic(this);
    }
  }
  /** Return a static child, which is created if necessary. */
  public ASTClass getStaticClass(String name,ClassKind kind){
    int N;
    N=dynamic_entries.size();
    for(int i=0;i<N;i++){
      if (dynamic_entries.get(i) instanceof ASTClass){
        ASTClass cl=(ASTClass)dynamic_entries.get(i);
        if (cl.name.equals(name)) throw new Error("class "+name+" already exists as a dynamic entry");
      }
    }
    N=static_entries.size();
    for(int i=0;i<N;i++){
      if (static_entries.get(i) instanceof ASTClass){
        ASTClass cl=(ASTClass)static_entries.get(i);
        if (cl.name.equals(name)) return cl;
      }
    }
    ASTClass res=new ASTClass(name,this,true,kind);
    res.setOrigin(new MessageOrigin("get static class"));
    return res;
  }

  /** Create a new named class from two block statements
   *  Do not forget to set the parent later! 
   */
  public ASTClass(String name,BlockStatement static_part,BlockStatement dynamic_part,ClassKind kind){
    this.kind=kind;
    this.name=name;
    int N=static_part.getLength();
    for(int i=0;i<N;i++){
      static_entries.add(static_part.getStatement(i));
    }
    N=dynamic_part.getLength();
    for(int i=0;i<N;i++){
      dynamic_entries.add(dynamic_part.getStatement(i));
    }    
  }

  public String getName(){
    return name;
  }
  public ASTClass getParentClass(){
    return parent_class;
  }
  public void setParentClass(ASTClass parent){
    this.parent_class=parent;
  }
  public void add_static(ASTNode n){
    static_entries.add(n);
    n.setParent(this);
    n.setStatic(true);
    while (n instanceof ASTWith){
      n=((ASTWith)n).body;
    }
    if (n instanceof ASTClass) {
      ((ASTClass)n).setParentClass(this);
    }
  }
  public void add_dynamic(ASTNode n){
    n.setParent(this);
    n.setStatic(false);
    dynamic_entries.add(n);
  }
  public int getStaticCount(){
    return static_entries.size();
  }
  public int getDynamicCount(){
    return dynamic_entries.size();
  }
  public ASTNode getStatic(int i){
    return static_entries.get(i);
  }
  public ASTNode getDynamic(int i){
    return dynamic_entries.get(i);
  }
  public boolean isPackage(){
    if (name==null) return true;
    if (kind!=ClassKind.Package) return false;
    if (dynamic_entries.size()>0) Abort("package with dynamic entries.");
    int N=static_entries.size();
    for(int i=0;i<N;i++){
      ASTNode tmp=static_entries.get(i);
      while (tmp instanceof ASTWith){
        tmp=((ASTWith)tmp).body;
      }
      if (!(tmp instanceof ASTClass)) Abort("package with non-class entries.");
    }
    return true;
  }

  /** Create a new class without putting it in a hierarchy. */
  public ASTClass(String name,ClassKind kind){
    this.kind=kind;
    this.name=name;
  }
  
  /** Accept a visitor.
   * @see ASTVisitor 
   */
  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }

  /** Perform a lookup of a full class name in a hierarchy.
   */
  public ASTClass find(String[] name){
    return find(name,0);
  }
  
  /** 
   * Auxiliary function for class lookup.
   */
  private ASTClass find(String[] name,int pos) {
    for(ASTNode n:static_entries){
      if (n instanceof ASTClass){
        ASTClass c=(ASTClass)n;
        if (c.name.equals(name[pos])){
          pos++;
          if (pos==name.length) return c;
          else return find(name,pos);
        }
      }
    }
    for(ASTNode n:dynamic_entries){
      if (n instanceof ASTClass){
        ASTClass c=(ASTClass)n;
        if (c.name.equals(name[pos])){
          pos++;
          if (pos==name.length) return c;
          else return find(name,pos);
        }
      }
    }
    return null;
  }
  private static Method find(List<ASTNode> list,String name, Type[] type){
    node:for(ASTNode n:list){
      if (n instanceof Method){
        Method m=(Method)n;
        if (m.getName().equals(name)){
          Debug("checking type of method %s%n",name);
          FunctionType t=m.getType();
          if (t.getArity()==type.length){
            for(int i=0;i<type.length;i++){
              if (!t.getArgument(i).supertypeof(type[i])){
                Debug("type of argument %d does not match (%s)%n",i,t.getArgument(i));
                continue node;
              }
            }
            return m;
          }
        }
      }
    }
    return null;
  }
  public Method find(String name, Type[] type) {
    //TODO: support inheritance and detect duplicate definitions.
    Method m=find(static_entries,name,type);
    if (m==null) m=find(dynamic_entries,name,type);
    return m;
  }

  private DeclarationStatement find_field(List<ASTNode> list,String name) {
    for(ASTNode n:list){
      if (n instanceof DeclarationStatement){
        DeclarationStatement d=(DeclarationStatement)n;
        if (d.getName().equals(name)){
          return d;
        } else {
          Debug("skipping field "+d.getName());
        }
      }
      if (n instanceof Method){
        Method m=(Method)n;
        Debug("skipping method "+m.getName());
      }
    }
    return null;
  }
  public DeclarationStatement find_field(String name) {
    Debug("looking for field "+name);
    DeclarationStatement stat=find_field(static_entries,name);
    DeclarationStatement dyn=find_field(dynamic_entries,name);
    if (dyn==null) {
      return stat;
    } else {
      return dyn;
    }
  }

  /** Get an iterator for the static fields of the class. */
  public Iterable<DeclarationStatement> staticFields() {
    return new FilteredIterable<ASTNode,DeclarationStatement>(static_entries,new DeclarationFilter());
  }
  
  /** Get an iterator for the dynamic fields of the class. */
  public Iterable<DeclarationStatement> dynamicFields() {
    return new FilteredIterable<ASTNode,DeclarationStatement>(dynamic_entries,new DeclarationFilter());
  }
  
  /** Get an iterator for the static methods of the class. */
  public Iterable<Method> staticMethods() {
    return new FilteredIterable<ASTNode,Method>(static_entries,new MethodFilter());
  }

  /** Get an iterator for the dynamic methods of the class. */
  public Iterable<Method> dynamicMethods() {
    return new FilteredIterable<ASTNode,Method>(dynamic_entries,new MethodFilter());
  }


}

