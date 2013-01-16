package vct.col.ast;

import hre.ast.MessageOrigin;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;

import vct.col.ast.ASTClass.ClassKind;
import vct.col.rewrite.AbstractRewriter;
import vct.col.util.ASTFactory;
import vct.col.util.FeatureScanner;
import vct.util.ClassName;

/**
 * Class for containing a collection of classes.
 *  
 * @author sccblom
 *
 */
public class ProgramUnit {

  private static HashMap<ClassName,ASTClass> library=new HashMap<ClassName, ASTClass>();
  
  static {
    ASTFactory create=new ASTFactory();
    create.setOrigin(new MessageOrigin("<<ProgramUnit>>"));
    ASTClass seq=create.ast_class("seq", ClassKind.Plain, null, null);
    Method len=create.function_decl(create.primitive_type(PrimitiveType.Sort.Integer), null, "length", new DeclarationStatement[0], null);
    seq.add_dynamic(len);
    library.put(new ClassName("seq"),seq);
  }
  
  /**
   * Classes that comprise this program unit. 
   */
  private HashMap<ClassName,ASTClass> classes=new HashMap<ClassName, ASTClass>();
  
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
  
  /**
   * Create an empty program unit.
   */
  public ProgramUnit(){
    
  }

  /**
   * Copy all entries from the given unit.
   * 
   * @param unit
   */
  public void merge(ProgramUnit unit){
    AbstractRewriter copy_rw=new AbstractRewriter(unit,this);
    copy_rw.rewriteAll();
  }

  public Iterable<ASTClass> classes() {
    return classes.values();
  }

  public Iterable<ClassName> classNames() {
    return classes.keySet();
  }

  public <T> void accept(ASTVisitor<T> visitor) {
    for(ASTClass cl:classes()){
      cl.accept(visitor);
    }
  }

  public ASTClass find(String[] name) {
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
    if (cl==null) return null;
    Method m=cl.find_predicate(nameFull[nameFull.length-1]);
    return m;
  }
}
