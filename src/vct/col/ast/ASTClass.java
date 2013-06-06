// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.ast.MessageOrigin;
import hre.util.FilteredIterable;

import java.util.*;

import javax.xml.transform.Source;

import vct.col.rewrite.MultiSubstitution;
import vct.col.util.DeclarationFilter;
import vct.col.util.MethodFilter;
import vct.util.ClassName;

import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Warning;

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
    Interface,
    Abstract,
    Plain,
    Kernel
  };
  
  /** contains the kind of class. */
  public final ClassKind kind;
  /** contains the name of the class/module/package. */
  public final String name;
  /** contains the classes extended by this class */
  public final ClassType super_classes[];
  /** contains the interfaces(classes) implemented by this class */
  public final ClassType implemented_classes[];
  /** contains the parent of this unit */
  private ASTClass parent_class;
  /** contains the static entries */
  private ArrayList<ASTNode> static_entries=new ArrayList<ASTNode>();
  /** contains the dynamic entries. */
  private ArrayList<ASTNode> dynamic_entries=new ArrayList<ASTNode>();
  /** contains the root of the source forest. */
  private ProgramUnit root;
  /** contains the package name */
  private ClassName package_name;
  
  public void attach(ProgramUnit root,ClassName package_name){
    this.root=root;
    this.package_name=package_name;
  }
  
  private void getFullName(ArrayList<String> fullname){
    if (parent_class!=null) parent_class.getFullName(fullname);
    if (name!=null) fullname.add(name); 
  }
  public String[] getFullName(){
    ArrayList<String> fullname=new ArrayList();
    getFullName(fullname);
    return fullname.toArray(new String[0]);
  }

  /** Create a root class from a given block statement. */
  public ASTClass(BlockStatement node) {
    kind=ClassKind.Plain;
    name="<<main>>";
    int N=node.getLength();
    for(int i=0;i<N;i++){
      static_entries.add(node.getStatement(i));
    }
    super_classes=new ClassType[0];
    implemented_classes=new ClassType[0];
  }

  /** Create a nested class. */
  public ASTClass(String name,ASTClass parent,boolean is_static,ClassKind kind){
    this.kind=kind;
    this.name=name;
    this.parent_class=parent;
    if(is_static){
      parent.add_static(this);
    } else {
      parent.add_dynamic(this);
    }
    super_classes=new ClassType[0];
    implemented_classes=new ClassType[0];
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
    super_classes=new ClassType[0];
    implemented_classes=new ClassType[0];
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
    if (n==null) return;
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
    if (n==null) return;
    n.setParent(this);
    n.setStatic(false);
    dynamic_entries.add(n);
    while (n instanceof ASTWith){
      n=((ASTWith)n).body;
    }
    if (n instanceof ASTClass) {
      ((ASTClass)n).setParentClass(this);
    }
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
  
  public ASTClass(String name,ClassKind kind){
    this(name,kind,new ClassType[0],new ClassType[0]);
  }

  /** Create a new class without putting it in a hierarchy. */
  public ASTClass(String name,ClassKind kind,ClassType bases[],ClassType supports[]){
    if (bases==null) Abort("super class array may not be null");
    if (supports==null) Abort("implemented array may not be null");
    this.kind=kind;
    this.name=name;
    super_classes=Arrays.copyOf(bases,bases.length);
    implemented_classes=Arrays.copyOf(supports,supports.length);
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
  private Method find(List<ASTNode> list,String name, ClassType object_type, Type[] type){
    node:for(ASTNode n:list){
      if (n instanceof Method){
        Method m=(Method)n;
        if (m.getName().equals(name)){
          Debug("checking type of method %s",name);
          DeclarationStatement args[]=m.getArgs();
          boolean varargs=m.usesVarArgs();
          if (args.length>=type.length || varargs){
            int idx;
            Debug("attempting match");
            MultiSubstitution sigma=m.getSubstitution(object_type);
            for(int i=0;i<type.length;i++){
              if (varargs && i>=args.length){
                idx=args.length-1;
              } else {
                idx=i;
              }
              Type m_idx_t=sigma.rewrite(m.getArgType(idx));
              if (!m_idx_t.supertypeof(root, type[i])){
                Debug("type of argument %d does not match method (cannot pass %s as %s)%n",i,type[i],m_idx_t);
                continue node;
              }
            }
            if (varargs && type.length==args.length-1) return m;
            for(int i=type.length;i<args.length;i++){
              if (!args[i].isValidFlag(ASTFlags.GHOST) || !args[i].getFlag(ASTFlags.GHOST)) {
                Debug("omitted argument is not ghost - no match");
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
  public Method find(String name, ClassType object_type, Type[] type) {
    return find(name,object_type,type,true);
  }
  public Method find(String name, ClassType object_type, Type[] type,boolean recursive) {
    //TODO: support inheritance and detect duplicate definitions.
    Method m=find(static_entries,name,object_type,type);
    if (m!=null) return m;
    m=find(dynamic_entries,name,object_type,type);
    if (m!=null) return m;
    if (recursive){
      for(ClassType parent:this.super_classes){
        m = root.find(parent).find(name,object_type,type);
        if (m != null) return m;
      }
    }  
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

  /**
   * Search for a field in the current class.
   * 
   * @deprecated Use find_field(name,false) instead.
   */
  @Deprecated
  public DeclarationStatement find_field(String name) {
    return find_field(name,false);    
  }
  /**
   * Search for a field declaration.
   * @param name The name of the field to be found.
   * @param recursive Flag that signals inclusion of super classes in the search path.
   * @return The Declaration of the field if found and null otherwise.
   */
  public DeclarationStatement find_field(String name,boolean recursive){
    Debug("looking for field "+name);
    DeclarationStatement temp=find_field(static_entries,name);
    if (temp!=null) return temp;
    temp=find_field(dynamic_entries,name);
    if (temp!=null) return temp;
    if (contract!=null){
      for(DeclarationStatement tmp : contract.given){
         if(tmp.getName().equals(name)) return tmp;
      }
    }
    if (!recursive) return temp;
    for(ClassType parent:this.super_classes){
      temp = root.find(parent).find_field(name,true);
      if (temp != null) return temp;
    }
    return null;
  }

  /** Get an iterator for all static members. */
  public Iterable<ASTNode> staticMembers(){
    return static_entries;
  }
  
  /** Get an iterator for all dynamic members. */
  public Iterable<ASTNode> dynamicMembers(){
    return dynamic_entries;
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
  
  private Contract contract;
  public Contract getContract(){
    return contract;
  }
  public void setContract(Contract contract){
    this.contract=contract;
    if (contract!=null){
      for(DeclarationStatement d:contract.given){
        d.setParent(this);
      }
      for(DeclarationStatement d:contract.yields){
        d.setParent(this);
      }
    }
  }
  public Method find_predicate(String string) {
    for(Method m:staticMethods()){
      if (m.getName().equals(string)) return m;
    }
    for(Method m:dynamicMethods()){
      if (m.getName().equals(string)) return m;
    }
    return null;
  }
}

