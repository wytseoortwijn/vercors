// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.ast.MessageOrigin;
import hre.util.FilteredIterable;

import java.util.*;

import vct.col.util.DeclarationFilter;
import vct.col.util.MethodFilter;

import static hre.System.Abort;

/** This class is the main container for declarations.
 *  For Java it contains both classes and packages.
 *  For PVL it contain both classes and the top level class list
 *  and block.
 * @author sccblom
 *
 */
public class ASTClass extends ASTNode {

  /** contains the name of the class/module/package. */
  private final String name;
  /** contains the parent of this unit */
  private ASTClass parent_class;
  /** contains the static entries */
  private ArrayList<ASTNode> static_entries=new ArrayList<ASTNode>();
  /** contains the dynamic entries. */
  private ArrayList<ASTNode> dynamic_entries=new ArrayList<ASTNode>();

  
  private void getFullName(ArrayList<String> fullname){
    if (parent_class!=null) parent_class.getFullName(fullname);
    System.err.print(" "+name);
    if (name!=null) fullname.add(name); 
  }
  public String[] getFullName(){
    ArrayList<String> fullname=new ArrayList();
    System.err.print("getting full name ");
    getFullName(fullname);
    System.err.println("");
    return fullname.toArray(new String[0]);
  }

  /** Create an empty root class. */
  public ASTClass(){
    name=null;
  }
  /** Create a root class from a given block statement. */
  public ASTClass(BlockStatement node) {
    name=null;
    int N=node.getLength();
    for(int i=0;i<N;i++){
      static_entries.add(node.getStatement(i));
    }
  }

  /** Create a new class in a hierarchy. */
  public ASTClass(String name,ASTClass parent,boolean is_static){
    this.name=name;
    this.parent_class=parent;
    if(is_static){
      parent.add_static(this);
    } else {
      parent.add_dynamic(this);
    }
  }
  /** Return a static child, which is created if necessary. */
  public ASTClass getStaticClass(String name){
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
    ASTClass res=new ASTClass(name,this,true);
    res.setOrigin(new MessageOrigin("get static class"));
    return res;
  }

  /** Create a new named class from two block statements
   *  Do not forget to set the parent later! 
   */
  public ASTClass(String name,BlockStatement static_part,BlockStatement dynamic_part){
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
    if (dynamic_entries.size()>0) return false;
    int N=static_entries.size();
    for(int i=0;i<N;i++){
      ASTNode tmp=static_entries.get(i);
      while (tmp instanceof ASTWith){
        tmp=((ASTWith)tmp).body;
      }
      if (!(tmp instanceof ASTClass)) return false;
    }
    return true;
  }
/***************************************************************************/
/* below this line is the legacy part that must be reviewed and rewritten. */
/***************************************************************************/

//  private Package pkg;
//  private HashMap<String,DeclarationStatement> fields=new HashMap();
//  private HashMap<String,Method> methods=new HashMap();
//  private ASTNode body=null;

//  public ASTClass(Package p,String name){
//    this.name=name;
//    pkg=p;
//    p.addClass(name,this);
//  }

  public ASTClass(String name){
    this.name=name;
  }
  
//  public Package getPackage(){ return pkg; }

  protected void addField(String name,DeclarationStatement d){
//    fields.put(name,d);
  }

  protected void addMethod(String name,Method m){
//    methods.put(name,m);
  }
  
  public Set<String> getMethods(){
//    return methods.keySet();
    return null;
  }
  
  public Set<String> getFields(){
//    return fields.keySet();
    return null;
  }
  
  public DeclarationStatement getField(String name){
//    return fields.get(name);
    return null;
  }

  public Method getMethod(String name){
//    return methods.get(name);
    return null;
  }
  
  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }

  private class BlockScanner extends AbstractVisitor {
    public void visit(Method m){
      addMethod(m.getName(),m);
    }
    public void visit(DeclarationStatement d){
      addField(d.getName(),d);
    }
  }

  public ASTClass find(String[] name){
    return find(name,0);
  }
  
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
          System.err.printf("checking type of method %s%n",name);
          FunctionType t=m.getType();
          if (t.getArity()==type.length){
            for(int i=0;i<type.length;i++){
              if (!t.getArgument(i).supertypeof(type[i])){
                System.err.printf("type of argument %d does not match (%s)%n",i,t.getArgument(i));
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
          System.err.println("skipping field "+d.getName());
        }
      }
      if (n instanceof Method){
        Method m=(Method)n;
        System.err.println("skipping method "+m.getName());
      }
    }
    return null;
  }
  public DeclarationStatement find_field(String name) {
    System.err.println("looking for field "+name);
    DeclarationStatement stat=find_field(static_entries,name);
    DeclarationStatement dyn=find_field(dynamic_entries,name);
    if (dyn==null) {
      return stat;
    } else {
      return dyn;
    }
  }

  public Iterable<DeclarationStatement> dynamicFields() {
    return new FilteredIterable<ASTNode,DeclarationStatement>(dynamic_entries,new DeclarationFilter());
  }
  
  public Iterable<Method> dynamicMethods() {
    return new FilteredIterable<ASTNode,Method>(dynamic_entries,new MethodFilter());
  }


}

