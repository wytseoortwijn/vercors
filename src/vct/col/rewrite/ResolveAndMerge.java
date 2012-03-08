package vct.col.rewrite;

import java.util.Stack;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTWith;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.FunctionType;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.util.AnyDefinition;
import vct.col.util.ClassDefinition;
import vct.col.util.DefinitionScanner;
import vct.col.util.FieldDefinition;
import vct.col.util.LocalDefinition;
import vct.col.util.MethodDefinition;
import vct.col.util.NameSpace;
import static hre.System.Abort;

/**
 * This rewriter changes assignment expressions to assignment statements.
 * 
 * @author Stefan Blom
 */ 
public class ResolveAndMerge extends AbstractRewriter {

  private ASTClass rootclass=null;
  private ClassDefinition defs;
  private Stack<ASTClass> currentstack;
  private ASTClass currentclass;
  private Method currentmethod;
  private NameSpace type_names;
  private NameSpace var_names;
  private NameSpace method_names;
  
  public void visit(ASTClass c) {
    String name=c.getName();
    if (c.getParentClass()==null){
      if (name!=null) throw new Error("root class with name "+name);
      if (rootclass!=null) throw new Error("nested class without parent");
      rootclass=new ASTClass();
      rootclass.setOrigin(c.getOrigin());
      currentstack=new Stack();
      currentclass=rootclass;
      defs=new ClassDefinition();
      DefinitionScanner scanner=new DefinitionScanner(defs);
      c.accept(scanner);
      type_names=new NameSpace();
      var_names=new NameSpace();
      method_names=new NameSpace();
      if (c.getDynamicCount()>0) throw new Error("root class with dynamic content");
      int N=c.getStaticCount();
      for(int i=0;i<N;i++){
        ASTNode res=c.getStatic(i).apply(this);
        if (res!=null && res.getParent()==null) rootclass.add_static(res);
      }
      ASTNode tmp=rootclass;
      rootclass=null;
      result=tmp;
      return;
    }
    if (name==null) {
      System.err.println("rewriting dummy package");
      if (c.getDynamicCount()>0) throw new Error("package with dynamic content");
      int N=c.getStaticCount();
      for(int i=0;i<N;i++){
        ASTNode res=c.getStatic(i).apply(this);
        if (res!=null && res.getParent()==null) currentclass.add_static(res);
      }
      return;
    }
    if (c.isPackage()){
      System.err.printf("rewriting %s package\n",name);
      if (c.getDynamicCount()>0) throw new Error("package with dynamic content");
      currentstack.push(currentclass);
      currentclass=currentclass.getStaticClass(name);
      int N=c.getStaticCount();
      for(int i=0;i<N;i++){
        ASTNode res=c.getStatic(i).apply(this);
        if (res!=null && res.getParent()==null) currentclass.add_static(res);
      }
      currentclass=currentstack.pop();
      return;      
    } else {
      System.err.println("rewriting class "+name);
      ASTClass res=new ASTClass(name);
      res.setOrigin(c.getOrigin());
      res.setParentClass(currentclass);
      currentstack.push(currentclass);
      currentclass=res;
      type_names.enter();
      var_names.enter();
      method_names.enter();
      ClassDefinition def=defs.lookupClass(res.getFullName());
      if (def==null) throw new Error("could not get def of current class.");
      System.err.printf("adding %s\n",name);
      type_names.add(name, def);
      for(ClassDefinition cldef:def.getClasses()){
        type_names.add(cldef.name,cldef);
      }
      for(FieldDefinition cldef:def.getFields()){
        var_names.add(cldef.name,cldef);
      }
      for(MethodDefinition cldef:def.getMethods()){
        method_names.add(cldef.name,cldef);
      }
      int N=c.getStaticCount();
      for(int i=0;i<N;i++){
        res.add_static(c.getStatic(i).apply(this));
      }
      int M=c.getDynamicCount();
      for(int i=0;i<M;i++){
        res.add_dynamic(c.getDynamic(i).apply(this));
      }
      currentclass=currentstack.pop();
      System.err.printf("leaving %s\n",name);
      type_names.leave();
      var_names.leave();
      method_names.leave();
      result=res;
      return;
    }
  }

  public void visit(ASTWith t){
    type_names.enter();
    var_names.enter();
    method_names.enter();
    switch(t.kind){
      case Classes:{
        ClassDefinition def=defs.lookupClass(t.from);
        if (def==null) throw new Error("cannot resolve import "+t.fromString()+" at "+t.getOrigin());
        if (t.all){
          for(ClassDefinition cldef:def.getClasses()){
            type_names.add(cldef.name,cldef);
          }
        } else {
          type_names.add(t.from[t.from.length-1],def);
        }
        break;
      }
      case Static:{
        throw new Error("cannot do static imports yet");
      }
    }
    result=t.body.apply(this);
    type_names.leave();
    var_names.leave();
    method_names.leave();
  }

  public void visit(ClassType t){
    ClassDefinition def=defs.lookupClass(t.name);
    if (def!=null) {
      result=t;
      return;
    }
    AnyDefinition tmp=type_names.lookup(t.name[0]);
    if (tmp!=null){
      if (tmp instanceof ClassDefinition){
        def=(ClassDefinition)tmp;
        String new_name[]=new String[def.full_name.length+t.name.length-1];
        for(int i=0;i<def.full_name.length;i++){
          new_name[i]=def.full_name[i];
        }
        int ofs=def.full_name.length-1;
        for(int i=1;i<t.name.length;i++){
          new_name[ofs+i]=t.name[i];
        }
        def=defs.lookupClass(new_name);
        if(def!=null){
          ClassType res=new ClassType(new_name);
          res.setOrigin(t.getOrigin());
          result=res;
          return;
        }
      } else {
        throw new Error("the name "+t.name[0]+" is " + tmp.getClass() + " instead of class at " + t.getOrigin());
      }
    }
    System.err.println("could not resolve class type "+t.getFullName());
    result=t;
  }
  
  public void visit(OperatorExpression e){
    StandardOperator op=e.getOperator();
    if (op==StandardOperator.Select||op==StandardOperator.GuardedSelect){
      ASTNode left=e.getArg(0).apply(this);
      ASTNode right=e.getArg(1);
      if (!(right instanceof NameExpression)) throw new Error("right hand side of select must be name");
      ((NameExpression)right).setKind(NameExpression.Kind.Field);
      ASTNode res=new OperatorExpression(op,left,right);
      res.setOrigin(e.getOrigin());
      result=res;
    } else {
      super.visit(e);
    }
  }

  public void visit(NameExpression e) {
    String name=e.getName();
    if (name.equals("null")){
      System.err.println("passing null");
      result=e;
      return;
    }
    if (e.getKind()==NameExpression.Kind.Reserved && (name.equals("\\result"))){
      result=create.reserved_name("\\result");
      if (currentmethod==null) Abort("current method is not set");
      result.setType(currentmethod.getType().getResult());
      return;
    }
    if (name.equals("super")) throw new Error("super not supported yet.");
    if (name.equals("this")){
      ClassType t=new ClassType(currentclass.getFullName());
      e.setType(t);
      System.err.println("passing this ("+t.getFullName()+")");
      result=e;
      return;
    }
    AnyDefinition def=var_names.lookup(name);
    if(def!=null){
      if (def instanceof FieldDefinition) {
        FieldDefinition fdef=(FieldDefinition)def;
        ClassType t=new ClassType(fdef.getParent().full_name);
        ASTNode space=create.this_expression(t);
        ASTNode new_name=create.field_name(name);
        result=create.expression(StandardOperator.Select,space,new_name);
        return;
      }
      if (def instanceof LocalDefinition) {
        LocalDefinition ldef=(LocalDefinition)def;
        e.setKind(NameExpression.Kind.Local);
        e.setType(ldef.getType());
        result=e;
        return;
      }
      throw new Error("bad kind of variables name "+def.getClass());
    }
    def=type_names.lookup(name);
    if(def!=null){
      if (def instanceof ClassDefinition) {
        ClassType t=new ClassType(((ClassDefinition)def).full_name);
        t.setOrigin(e);
        result=t;
        return;
      }
      throw new Error("bad kind of type name "+def.getClass());
    }
    def=method_names.lookup(name);
    if(def!=null){
      if (def instanceof MethodDefinition) {
        e.setKind(NameExpression.Kind.Method);
        result=e;
        return;
      }
      throw new Error("bad kind of method name "+def.getClass());
    }
    throw new Error("could not resolve name "+e.getName()+" at "+e.getOrigin());
  }

  @Override
  public void visit(DeclarationStatement s) {
    String name=s.getName();
    ASTNode parent=s.getParent();
    if (parent==null) throw new Error("parent of declaration statement must be set.");
    if (parent instanceof ASTClass){
      // has already been added.
    } else if (parent instanceof BlockStatement){
      var_names.add(name,new LocalDefinition(name,s.getType()));
    } else {
      throw new Error("unexpected parent "+parent.getClass());
    }
    super.visit(s);
  }
  
  public void visit(Method m){
    if (currentmethod!=null) Abort("nestedmethod");
    currentmethod=m;
    type_names.enter();
    var_names.enter();
    method_names.enter();
    int N=m.getArity();
    FunctionType t=m.getType();
    for(int i=0;i<N;i++){
      String name=m.getArgument(i);
      var_names.add(name,new LocalDefinition(name,t.getArgument(i)));
    }
    super.visit(m);
    type_names.leave();
    var_names.leave();
    method_names.leave();
    currentmethod=null;
  }
  
  public void visit(MethodInvokation e){
    ASTNode object=e.object;
    NameExpression method=e.method;
    String name=method.getName();
    if (object==null){
      object=create.reserved_name("this");
      ClassType t=new ClassType(currentclass.getFullName());
      object.setType(t);
    } else {
      object=object.apply(this);
    }
    method=create.method_name(name);
    boolean guarded=e.guarded;
    
    int N=e.getArity();
    ASTNode args[]=new ASTNode[N];
    for(int i=0;i<N;i++){
      args[i]=e.getArg(i).apply(this);
    }
    result=create.invokation(object, guarded, method, args);
  }
}
