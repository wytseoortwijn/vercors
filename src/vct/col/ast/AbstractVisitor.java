// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

import vct.util.ClassName;


/**
 * Abstract AST visitor implementation which can skip cases and
 * distinguish between bad input and missing cases.
 * 
 * @author sccblom
 *
 */
public abstract class AbstractVisitor<T> extends ASTFrame<T> implements ASTVisitor<T> {
/*
  Note: need a good way of creating and abstract class that will
  allow defining both valid input cases and cases which are ignored
  on purpose. Maybe a not only the 'case' equivalent but also
  a 'recursive' default would be useful.
*/
    
  protected Stack<ClassName> current_class_stack=new Stack();
  protected ClassName current_class=null;
  
  private Set<java.lang.Class> valid_classes;
  
  public AbstractVisitor(){
    this(null,null);
  }

/*
  public AbstractVisitor(Set<java.lang.Class> valid_classes){
    this(null,valid_classes);
  }


  public AbstractVisitor(ProgramUnit source,Set<java.lang.Class> valid_classes){
    this.source=source;
    if (valid_classes==null){
      this.valid_classes=null;
    } else {
      this.valid_classes=new HashSet();
      this.valid_classes.addAll(valid_classes);
    }
  }
  
  public AbstractVisitor(ProgramUnit source) {
    this(source,null);
  }

  good idea, but does not work well: hard to get classes.
  public AbstractVisitor(Set<java.lang.Class> valid_classes,Set<java.lang.Class> skip_classes){
    this.valid_classes=new HashSet();
    this.valid_classes.addAll(valid_classes);
    this.skip_classes=new HashSet();
    this.skip_classes.addAll(skip_classes);
  }
*/
  
  public AbstractVisitor(ProgramUnit source) {
    super(source);
  }
  
  public AbstractVisitor(ProgramUnit source,ProgramUnit target) {
    super(source,target);
  }
  
  public AbstractVisitor(ASTFrame shared) {
    super(shared);
  }
 
  private final void visit_any(ASTNode any){
    java.lang.Class<? extends Object> any_class=any.getClass();
    //if (skip_classes.contains(any.getClass())) return;
    System.err.printf("for origin %s%n",any.getOrigin());
    if (valid_classes==null) {
      throw new Error("missing case or invalid AST: "+any_class.getSimpleName()+" in "+this.getClass().getSimpleName());
    }
    if (valid_classes.contains(any.getClass())){
      throw new Error("invalid AST");
    } else {
      throw new Error("missing case");
    }
  }
  
  public void pre_visit(ASTNode n){
    this.enter(n);
    if (n instanceof ASTClass){
      // set current class and push.
      current_class=new ClassName(((ASTClass)n).getFullName());
      current_class_stack.push(current_class);
    }
  }
  
  public void post_visit(ASTNode n){
    this.leave(n);
    if (n instanceof ASTClass){
      // pop current class and reset.
      current_class_stack.pop();
      if (current_class_stack.isEmpty()){
        current_class=null;
      } else {
        current_class=current_class_stack.peek();
      }
    }
  }
  
  public void visit(StandardProcedure p){ visit_any(p); }

  public void visit(ConstantExpression e){ visit_any(e); }
  
  public void visit(OperatorExpression e){ visit_any(e); }
  
  public void visit(NameExpression e){ visit_any(e); }

  public void visit(ArrayType t){ visit_any(t); }

  public void visit(ClassType t){ visit_any(t); }
  
  public void visit(FunctionType t){ visit_any(t); }
  
  public void visit(PrimitiveType t){ visit_any(t); }
  
  public void visit(RecordType t){ visit_any(t); }

  public void visit(MethodInvokation e){ visit_any(e); }

  public void visit(BlockStatement s){ visit_any(s); }
  
  public void visit(IfStatement s){ visit_any(s); }
  
  public void visit(ReturnStatement s){ visit_any(s); }
  
  public void visit(AssignmentStatement s){ visit_any(s); }

  public void visit(DeclarationStatement s){ visit_any(s); }

  public void visit(LoopStatement s){ visit_any(s); }

  public void visit(Method m){ visit_any(m); }

  public void visit(ASTClass c){ visit_any(c); }
  
  public void visit(ASTWith with){ visit_any(with); }
  
  public void visit(BindingExpression e){ visit_any(e); }
}


