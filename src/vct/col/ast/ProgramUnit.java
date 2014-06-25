package vct.col.ast;

import hre.ast.MessageOrigin;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;

import vct.col.ast.ASTClass.ClassKind;
import vct.col.rewrite.AbstractRewriter;
import vct.col.util.ASTFactory;
import vct.col.util.FeatureScanner;
import vct.util.ClassName;
import static hre.System.*;

/**
 * Class for containing a collection of classes.
 *  
 * @author sccblom
 *
 */
public class ProgramUnit {

  private SpecificationFormat format=SpecificationFormat.Concurrent;
  
  public void setSpecificationFormat(SpecificationFormat format){
    this.format=format;
  }
  
  public SpecificationFormat getSpecificationFormat(){
    return format;
  }
  
  private static HashMap<ClassName,ASTClass> library=new HashMap<ClassName, ASTClass>();
  
  static {
    ASTFactory create=new ASTFactory();
    create.setOrigin(new MessageOrigin("<<ProgramUnit>>"));
    ASTClass seq=create.ast_class("seq", ClassKind.Plain, null, null);
    Method len=create.function_decl(create.primitive_type(PrimitiveType.Sort.Integer), null, "length", new DeclarationStatement[0], null);
    seq.add_dynamic(len);
    library.put(new ClassName("seq"),seq);
    //ASTClass var=create.ast_class("var", ClassKind.Plain, null, null);
    
  }

  /**
   * The compilation units that make up this program/subsystem.
   */
  private ArrayList<CompilationUnit> contents=new ArrayList<CompilationUnit>();
  
  
  public int size(){
    return contents.size();
  }
  
  public CompilationUnit get(int i){
    return contents.get(i);
  }
  
  public Iterable<CompilationUnit> get(){
    return contents;
  }
  
  /**
   * Index of classes that are contained within this program unit. 
   */
  HashMap<ClassName,ASTClass> classes=new HashMap<ClassName, ASTClass>();
  
  /**
   * Index of declarations that are contained within this program unit. 
   */
  private HashMap<ClassName,ASTDeclaration> decl_map=new HashMap<ClassName,ASTDeclaration>();
  
  
  private HashMap<ClassName,Method> adt_map=new HashMap<ClassName,Method>();
  
  /*
  public void addClass(ClassName name,ASTClass cl){
    classes.put(name,cl);
    cl.attach(this,name);
  }
  
  public void addClass(String name[],ASTClass cl){
    addClass(new ClassName(name),cl);
  }
  
  public void addClass(ClassType type,ASTClass cl){
    addClass(type.getNameFull(),cl);
  }
  */
  
  /**
   * Create an empty program unit.
   */
  public ProgramUnit(){
    
  }

  public void add(CompilationUnit unit){
    contents.add(unit);
    for(ASTNode n:unit.get()){
      if (n instanceof ASTDeclaration){
        ASTDeclaration d=(ASTDeclaration)n;
        decl_map.put(d.getDeclName(), d);
      }
      if (n instanceof ASTClass){
        ASTClass cl=(ASTClass)n;
        Debug("indexing %s as %s",cl.name,cl.getDeclName());
        classes.put(cl.getDeclName(),cl);
        for(Method m : cl.staticMethods()){
          if (m.kind==Method.Kind.Predicate){
            decl_map.put(m.getDeclName(),m);
          }          
        }
        for(Method m : cl.dynamicMethods()){
          if (m.kind==Method.Kind.Predicate){
            decl_map.put(m.getDeclName(),m);
          }
        }
      }
      if (n instanceof AxiomaticDataType) {
        AxiomaticDataType adt=(AxiomaticDataType)n;
        for(Method m:adt.constructors()){
          Warning("putting adt entry %s",m.getDeclName().toString("."));
          adt_map.put(m.getDeclName(),m);
        }
        for(Method m:adt.mappings()){
          adt_map.put(m.getDeclName(),m);
        }
      }
    }
  }

  public Iterable<ASTClass> classes() {
    return classes.values();
  }

  public Iterable<ClassName> classNames() {
    return classes.keySet();
  }

  public <T> void accept(ASTVisitor<T> visitor) {
    for(CompilationUnit cu:contents){
      cu.accept(visitor);
    }
  }

  public ASTClass find(String ... name) {
    return find(new ClassName(name));
  }

  public ASTClass find(ClassName name) {
    ASTClass cl=classes.get(name);
    if (cl==null){
      cl=library.get(name);
    }
    return cl;
  }

  public ASTClass find(ClassType type) {
    return find(new ClassName(type.getNameFull()));
  }

  public Method find_predicate(String[] nameFull) {
    String [] class_name=Arrays.copyOf(nameFull, nameFull.length-1);
    ASTClass cl=find(class_name);
    if (cl==null) {
      Debug("class %s not found",class_name[class_name.length-1]);
      return null;
    }
    Method m=cl.find_predicate(nameFull[nameFull.length-1]);
    if (m==null){
      Debug("predicate %s not found in class %s",nameFull[nameFull.length-1],class_name[0]);
    }
    return m;
  }

  public ASTDeclaration find_decl(String[] nameFull) {
    ClassName class_name=new ClassName(nameFull);
    return decl_map.get(class_name);
  }
  
  public Method find_adt(String ... nameFull) {
    ClassName class_name=new ClassName(nameFull);
    return adt_map.get(class_name);
  }
}
