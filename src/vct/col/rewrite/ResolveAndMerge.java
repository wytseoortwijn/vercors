package vct.col.rewrite;

import hre.util.SingleNameSpace;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTWith;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Dereference;
import vct.col.ast.FunctionType;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.util.AnyDefinition;
import vct.col.util.ClassDefinition;
import vct.col.util.DefinitionScanner;
import vct.col.util.FieldDefinition;
import vct.col.util.LocalDefinition;
import vct.col.util.MethodDefinition;
import vct.col.util.PredicateScanner;
import vct.util.ClassName;
import static hre.System.*;

/**
 * This rewriter changes assignment expressions to assignment statements.
 * 
 * @author Stefan Blom
 */ 
public class ResolveAndMerge extends AbstractRewriter {

  public ResolveAndMerge(ProgramUnit source) {
    super(source);
    currentstack=new Stack();
    currentclass=null;
    defs=new ClassDefinition();
    DefinitionScanner scanner=new DefinitionScanner(defs);
    source.accept(scanner);
    source.accept(new PredicateScanner(predicates));
    type_names=new SingleNameSpace();
    var_names=new SingleNameSpace();
    method_names=new SingleNameSpace();
  }

  private AbstractRewriter copy_rw=new AbstractRewriter(source(),target());
  
  private ClassDefinition defs;
  private Stack<ASTClass> currentstack;
  private ASTClass currentclass;
  private Method currentmethod;
  private SingleNameSpace<String,Type> type_names;
  private SingleNameSpace<String,AnyDefinition> var_names;
  private SingleNameSpace<String,AnyDefinition> method_names;
  private Set<ClassName> predicates=new HashSet();
  
  private boolean static_context=true;
  private boolean StaticContext(){
    return static_context;
  }
  
  public void post_visit(ASTNode n){
    if (n.get_before()!=null && result.get_before()==null){
      ASTNode tmp=result;
      BlockStatement orig=n.get_before();
      BlockStatement modified=create.block();
      int N=orig.getLength();
      for(int i=0;i<N;i++){
        ASTNode s=orig.getStatement(i);
        if (s instanceof AssignmentStatement) {
          AssignmentStatement a=(AssignmentStatement)s;
          modified.add_statement(create.assignment(s.getOrigin(),
                  a.getLocation().apply(copy_rw),
                  a.getExpression().apply(this)));
        } else if (s instanceof OperatorExpression) {
          OperatorExpression a=(OperatorExpression)s;
          if (a.getOperator()!=StandardOperator.Assign){
            Abort("bad expression in with block at %s",s.getOrigin());
          }
          modified.add_statement(create.assignment(s.getOrigin(),
                a.getArg(0).apply(copy_rw),
                a.getArg(1).apply(this)));            
        } else {
          Abort("unexpected %s in with block at %s",s.getClass(),s.getOrigin());
        }
      }
      tmp.set_before(modified);
      result=tmp;
    }
    if (n.get_after()!=null && result.get_after()==null){
      ASTNode tmp=result;
      BlockStatement orig=n.get_after();
      BlockStatement modified=create.block();
      int N=orig.getLength();
      for(int i=0;i<N;i++){
        ASTNode s=orig.getStatement(i);
        if (s instanceof AssignmentStatement) {
          AssignmentStatement a=(AssignmentStatement)s;
          modified.add_statement(create.assignment(s.getOrigin(),
                  a.getLocation().apply(this),
                  a.getExpression().apply(copy_rw)));
        } else if (s instanceof OperatorExpression) {
          OperatorExpression a=(OperatorExpression)s;
          switch(a.getOperator()){
            case Assign:
              modified.add_statement(create.assignment(s.getOrigin(),
                  a.getArg(0).apply(this),
                  a.getArg(1).apply(copy_rw)));
              break;
            case Unfold:
              modified.add_statement(s.apply(copy_rw));
              break;
            default:
              Abort("bad expression in after block at %s",s.getOrigin());
          }
        } else {
          Abort("unexpected %s in after block at %s",s.getClass(),s.getOrigin());
        }
      }
      tmp.set_after(modified);
      result=tmp;
    }
    super.post_visit(n);
  }
  public void visit(ASTClass c) {
    String name=c.getName();
    Debug("rewriting class %s",name);
    ASTClass res=new ASTClass(
      name,
      c.kind,
      rewrite(c.super_classes),
      rewrite(c.implemented_classes)
    );
    res.setOrigin(c.getOrigin());
    res.setParentClass(currentclass);
    currentstack.push(currentclass);
    currentclass=res;
    type_names.enter();
    var_names.enter();
    method_names.enter();
    ClassDefinition def=defs.lookupClass(res.getFullName());
    if (def==null) throw new Error("could not get def of current class.");
    Debug("adding %s",name);
    type_names.add(name,create.class_type(current_class.name));
    // nested classes?
    //for(ClassDefinition cldef:def.getClasses()){
    //  type_names.add(cldef.name,cldef);
    //}
    for(FieldDefinition cldef:def.getFields()){
      var_names.add(cldef.name,cldef);
    }
    for(MethodDefinition cldef:def.getMethods()){
      method_names.add(cldef.name,cldef);
    }
    Contract contract=c.getContract();
    if (contract !=null){
      // TODO: filter type arguments.
      //for (DeclarationStatement decl:contract.given){
      //  Warning("adding type argument %s",decl.getName());
      //  type_names.add(decl.getName(),new ClassDefinition(decl.getName()));
      //}
      res.setContract(rewrite(contract));
    }
    int N=c.getStaticCount();
    for(int i=0;i<N;i++){
      static_context=true;
      res.add_static(c.getStatic(i).apply(this));
    }
    int M=c.getDynamicCount();
    for(int i=0;i<M;i++){
      static_context=false;
      res.add_dynamic(c.getDynamic(i).apply(this));
    }
    currentclass=currentstack.pop();
    Debug("leaving %s",name);
    type_names.leave();
    var_names.leave();
    method_names.leave();
    result=res;
    return;
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
            type_names.add(cldef.name,new ClassType(cldef.full_name));
          }
        } else {
          type_names.add(t.from[t.from.length-1],new ClassType(def.full_name));
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
    String t_name[]=t.getNameFull();
    {
      ClassDefinition def=defs.lookupClass(t_name);
      if (def!=null) {
        result=t;
        return;
      }
    }
    Type tmp=type_names.lookup(t_name[0]);
    if (tmp!=null){
      if (tmp instanceof ClassType){
        String full_name[]=((ClassType)tmp).getNameFull();
        String new_name[]=new String[full_name.length+t_name.length-1];
        for(int i=0;i<full_name.length;i++){
          new_name[i]=full_name[i];
        }
        int ofs=full_name.length-1;
        for(int i=1;i<t_name.length;i++){
          new_name[ofs+i]=t_name[i];
        }
        {
          ClassType res=new ClassType(new_name);
          res.setOrigin(t.getOrigin());
          result=res;
          return;
        }
      } else {
        throw new Error("the name "+t_name[0]+" is " + tmp.getClass() + " instead of class at " + t.getOrigin());
      }
    }
    if (!predicates.contains(new ClassName(t.getNameFull()))){
      Fail("could not resolve class type %s at %s",t.getFullName(),t.getOrigin());
    }
    result=create.class_type(t.getNameFull());
  }
  
  public void visit(NameExpression e) {
    String name=e.getName();
    if (name.equals("null")){
      Debug("passing null");
      result=e;
      return;
    }
    switch(e.getKind()){
      case Label:
      Warning("skipping resolving of label %s",name);
      result=create.label(name);
      return;
    default:
      break;
    }
    if (e.getKind()==NameExpression.Kind.Reserved && (name.equals("\\result"))){
      result=create.reserved_name("\\result");
      if (currentmethod==null) Abort("current method is not set");
      result.setType(currentmethod.getReturnType());
      return;
    }
    if (name.equals("super")) throw new Error("super not supported yet.");
    if (name.equals("this")){
      ClassType t=new ClassType(currentclass.getFullName());
      e.setType(t);
      Debug("passing this ("+t.getFullName()+")");
      result=e;
      return;
    }
    AnyDefinition def=var_names.lookup(name);
    if(def!=null){
      if (def instanceof FieldDefinition) {
        FieldDefinition fdef=(FieldDefinition)def;      
        ClassType t=create.class_type(fdef.getParent().full_name);
        ASTNode space;
        if(fdef.is_static){
          space=t;
        } else {
          space=create.this_expression(t);
        }
        result=create.dereference(space,name);
        return;
      }
      if (def instanceof LocalDefinition) {
        LocalDefinition ldef=(LocalDefinition)def;
        e.setKind(ldef.getKind());
        e.setType(ldef.getType());
        result=e;
        return;
      }
      Fail("bad kind of variables name "+def.getClass()+" at "+e.getOrigin());
    }
    Type cl_name=type_names.lookup(name);
    if(cl_name!=null){
      if (cl_name instanceof ClassType) {
        ClassType t=new ClassType(((ClassType)cl_name).getNameFull());
        t.setOrigin(e);
        result=t;
        return;
      }
      Fail("cannot use type "+cl_name.getClass()+" as name at "+e.getOrigin());
    }
    def=method_names.lookup(name);
    if(def!=null){
      if (def instanceof MethodDefinition) {
        e.setKind(NameExpression.Kind.Method);
        result=e;
        return;
      }
      Fail("bad kind of method name "+def.getClass()+" at "+e.getOrigin());
    }
    if (currentmethod!=null && currentmethod.getContract()!=null){
      Contract c=currentmethod.getContract();
      if (c.hasLabel(name)){
        result=create.label(name);
        return;
      }
    }
    Fail("could not resolve name "+e.getName()+" at "+e.getOrigin());
  }

  @Override
  public void visit(DeclarationStatement s) {
    String name=s.getName();
    ASTNode parent=s.getParent();
    if (parent==null) throw new Error("parent of declaration statement must be set at "+s.getOrigin());
    if (parent instanceof ASTClass ||parent instanceof Method){
      // has already been added.
    } else if (parent instanceof BlockStatement){
      var_names.add(name,new LocalDefinition(name,NameExpression.Kind.Local,s.getType()));
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
    for(int i=0;i<N;i++){
      String name=m.getArgument(i);
      var_names.add(name,new LocalDefinition(name,NameExpression.Kind.Argument,m.getArgType(i)));
    }

    String name=m.getName();
    DeclarationStatement args[]=rewrite(m.getArgs());
    Contract mc=m.getContract();
    ContractBuilder cb=new ContractBuilder();
    if (mc!=null){
      for(DeclarationStatement d:mc.given){
        String var=d.getName();
        var_names.add(var,new LocalDefinition(var,NameExpression.Kind.Argument,d.getType()));
        cb.given(rewrite(d));
      }
      cb.requires(rewrite(mc.pre_condition));
      for(DeclarationStatement d:mc.yields){
        String var=d.getName();
        var_names.add(var,new LocalDefinition(var,NameExpression.Kind.Argument,d.getType()));
        cb.yields(rewrite(d));
      }
      cb.ensures(rewrite(mc.post_condition));
      if (mc.modifies!=null) cb.modifies(rewrite(mc.modifies));
    }
    Method.Kind kind=m.kind;
    Type rt=rewrite(m.getReturnType());
    ASTNode body=rewrite(m.getBody());
    Method res=new Method(kind,name,rt,cb.getContract(),args,body);
    res.setOrigin(m.getOrigin());
    result=res;
    
    type_names.leave();
    var_names.leave();
    method_names.leave();
    currentmethod=null;
  }
  
  public void visit(MethodInvokation e){
    ASTNode object=e.object;
    NameExpression method=e.method;
    String name=method.getName();
    Debug("invokation %s",name); 
    for (NameExpression lbl:e.getLabels()){
      Debug("invokation %s has label %s",name,lbl);
      String var=lbl.getName();
      var_names.add(var,new LocalDefinition(var,NameExpression.Kind.Label,new ClassType("<<label>>")));
    }
    if (object==null){
      // TODO: check for static import.
      if (StaticContext()){
        ClassType t=create.class_type(currentclass.getFullName());
        object=t;
        object.setType(t); 
      } else {
        object=create.reserved_name("this");
        ClassType t=new ClassType(currentclass.getFullName());
        object.setType(t);
      }
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
  
  public void visit(LoopStatement s){
    super.visit(s);
    result.set_before(copy_rw.rewrite(s.get_before()));
    result.set_after(rewrite(s.get_after()));
  }
}
