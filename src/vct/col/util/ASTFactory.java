// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.util;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTVisitor;
import vct.col.ast.ASTWith.Kind;
import vct.col.ast.ASTWith;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.BindingExpression;
import vct.col.ast.BindingExpression.Binder;
import vct.col.ast.ClassType;
import vct.col.ast.ConstantExpression;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.IfStatement;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ReturnStatement;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.ast.BlockStatement;
import hre.ast.Origin;
import hre.util.FrameControl;
import hre.util.FrameReference;
import static hre.System.*;

/**
 * This class provides a factory for ASTNodes, that can be
 * configured to (semi-)automatically insert origins.
 * 
 * For every AST construction method, this class contains three variants that
 * are different upon how the origin is specified:
 * <ul>
 * <li>The core version of every construction method, explicitly passes the origin.
 * <li>The stack version calls the core version, passing the current origin.
 * <li>The extracting version calls the core version, with passing the extracted origin.
 * </ul>
 * Note that extracting origins form any class that is itself an origin does not work:
 * the core constructor would be invoked instead of the extracting one. 
 * 
 * @author sccblom
 * @param E The type of object from which this factory can extract origins.
 */
public class ASTFactory<E> implements FrameControl {
  
  /**
   * The stack of origins that this factory uses.
   */
  private final FrameReference<Origin> origin_stack=new FrameReference<Origin>();

  /**
   * Factory class that can extract origins.
   * This variable may be null;
   */
  private OriginFactory<E> origin_source=null;
  
  /**
   * Visitor to be called immediately after construction of a new node.
   * This variable may be null;
   */
  private ASTVisitor post=null;
  
  /**
   * Create a new AST factory.
   */
  public ASTFactory(){}

  /**
   * Create a new factory that perform a post check on every new node.
   */
  public ASTFactory(ASTVisitor post){
    this.post=post;
  }

  /**
   * Create a new AST factory that can extract origins from <code>E</code> objects.
   */
  public ASTFactory(OriginFactory<E> factory){
    origin_source=factory;
  }

  /**
   * Replace the current origin. 
   */
  public void setOrigin(Origin origin) {
    this.origin_stack.set(origin);
  }
  
  /**
   * Replace the current origin with the extracted origin.
   */
  public void setOrigin(E source) {
    this.origin_stack.set(origin_source.create(source));
  }
  
  /**
   * Get the current origin. 
   */
  public Origin getOrigin() {
    return origin_stack.get();
  }
  
  /**
   * Enter a new stack frame of the origin stack.
   */
  public void enter(){
    origin_stack.enter();
  }
  
  /**
   * Leave the current stack frame of the origin stack.
   */
  public void leave(){
    origin_stack.leave();
  }

  /**
   * Create an assignment statement/expression.
   */
  public ASTNode assignment(Origin origin,ASTNode loc, ASTNode val) {
    AssignmentStatement res=new AssignmentStatement(loc,val);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public ASTNode assignment(ASTNode loc, ASTNode val) {
    return assignment(origin_stack.get(),loc,val);
  }
  public ASTNode assignment(E origin,ASTNode loc, ASTNode val) {
    return assignment(origin_source.create(origin),loc,val);
  }
  
  /**
   * Create a new class.
   */
  public ASTClass ast_class(Origin origin,String name,ClassKind kind,ClassType bases[],ClassType supports[]) {
    if (bases==null) bases=new ClassType[0];
    if (supports==null) supports=new ClassType[0];
    ASTClass res=new ASTClass(name,kind,bases,supports);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;    
  }
  public ASTClass ast_class(String name,ClassKind kind,ClassType bases[],ClassType supports[]) {
    return ast_class(origin_stack.get(),name,kind,bases,supports);
  }
  public ASTClass ast_class(E origin,String name,ClassKind kind,ClassType bases[],ClassType supports[]) {
    return ast_class(origin_source.create(origin),name,kind,bases,supports);
  }
  
  /**
   * Create a new plain class.
   */
  public ASTClass new_class(Origin origin,String name,ClassType super_class,ClassType ... supports) {
    ClassType bases[]={super_class};
    if (super_class==null) bases=null;
    return ast_class(origin,name,ClassKind.Plain,bases,supports);
  }
  public ASTClass new_class(String name,ClassType super_class,ClassType ... supports) {
    return new_class(origin_stack.get(),name,super_class,supports);
  }
  public ASTClass plain_class(E origin,String name,ClassType super_class,ClassType ... supports) {
    return new_class(origin_source.create(origin),name,super_class,supports);
  }
  
  
  /**
   * Create a new abstract class.
   */
  public ASTClass abstract_class(Origin origin,String name,ClassType super_class,ClassType ... supports) {
    ClassType bases[]={super_class};
    if (super_class==null) bases=null;
    return ast_class(origin,name,ClassKind.Abstract,bases,supports);
  }
  public ASTClass abstract_class(String name,ClassType super_class,ClassType ... supports) {
    return abstract_class(origin_stack.get(),name,super_class,supports);
  }
  public ASTClass abstract_class(E origin,String name,ClassType super_class,ClassType ... supports) {
    return abstract_class(origin_source.create(origin),name,super_class,supports);
  }
  

  /**
   * Create a new block, with the given statements as (initial) contents.
   */
  public BlockStatement block(Origin origin, ASTNode ... args) {
    BlockStatement res=new BlockStatement();
    for(ASTNode node:args){
      res.add_statement(node);
    }
    res.setOrigin(origin);
    res.accept_if(post);
    return res;        
  }
  public BlockStatement block(E origin,ASTNode ... args) {
    return block(origin_source.create(origin),args);
  }
  public BlockStatement block(ASTNode ... args) {
    return block(origin_stack.get(),args);
  }


  /**
   * Create a new class type node.
   */
  public ClassType class_type(Origin origin,String ... name){
    ClassType res=new ClassType(name);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public ClassType class_type(E origin,String ... name){
    return class_type(origin_source.create(origin),name);
  }
  public ClassType class_type(String ... name){
    return class_type(origin_stack.get(),name);
  }

  /**
   * Create a new string constant.
   */
  public ConstantExpression constant(Origin origin, String s) {
    ConstantExpression res=new ConstantExpression(s,origin);
    res.accept_if(post);
    return res;    
  }
  public ConstantExpression constant(E origin,String s) {
    return constant(origin_source.create(origin),s);
  }
  public ConstantExpression constant(String s) {
    return constant(origin_stack.get(),s);
  }

  /**
   * Create a new boolean constant.
   */
  public ConstantExpression constant(Origin origin, boolean b) {
    ConstantExpression res=new ConstantExpression(b,origin);
    res.accept_if(post);
    return res;    
  }
  public ConstantExpression constant(E origin,boolean b) {
    return constant(origin_source.create(origin),b);
  }
  public ConstantExpression constant(boolean b) {
    return constant(origin_stack.get(),b);
  }
  
  /**
   * Create a new integer constant.
   */
  public ConstantExpression constant(Origin origin, int i) {
    ConstantExpression res=new ConstantExpression(i,origin);
    res.accept_if(post);
    return res;    
  }
  public ConstantExpression constant(E origin,int i) {
    return constant(origin_source.create(origin),i);
  }
  public ConstantExpression constant(int i) {
    return constant(origin_stack.get(),i);
  }
  
  /**
   * Create a new long constant.
   */
  public ConstantExpression constant(Origin origin, long i) {
    ConstantExpression res=new ConstantExpression(i,origin);
    res.accept_if(post);
    return res;    
  }
  public ConstantExpression constant(E origin,long i) {
    return constant(origin_source.create(origin),i);
  }
  public ConstantExpression constant(long i) {
    return constant(origin_stack.get(),i);
  }
  /**
   * Create a new double constant.
   */
  public ConstantExpression constant(Origin origin, double i) {
    ConstantExpression res=new ConstantExpression(i,origin);
    res.accept_if(post);
    return res;    
  }
  public ConstantExpression constant(E origin,double i) {
    return constant(origin_source.create(origin),i);
  }
  public ConstantExpression constant(double i) {
    return constant(origin_stack.get(),i);
  }

  /**
   * Create a new operator expression.
   */
  public OperatorExpression expression(Origin origin,StandardOperator op, ASTNode ... args){
    if (op==null) Abort("null operator at %s",origin);
    if (args==null) Abort("null arguments at %s",origin);
    OperatorExpression res=new OperatorExpression(op,args);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public OperatorExpression expression(E origin,StandardOperator op, ASTNode ... args){
    return expression(origin_source.create(origin),op,args);
  }
  public OperatorExpression expression(StandardOperator op, ASTNode ... args){
    return expression(origin_stack.get(),op,args);
  }
  
  /**
   * Create a new variable declaration.
   * 
   * Used for members, arguments and local variables. 
   */
  public DeclarationStatement field_decl(Origin origin,String name, Type type) {
    DeclarationStatement res=new DeclarationStatement(name,type);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;    
  }
  public DeclarationStatement field_decl(E origin,String name, Type type) {
    return field_decl(origin_source.create(origin),name,type);
  }
  public DeclarationStatement field_decl(String name, Type type) {
    return field_decl(origin_stack.get(),name,type);
  }
  
  /**
   * Create a new variable declaration with default value.
   * 
   * Used for members, arguments and local variables. 
   */
  public DeclarationStatement field_decl(Origin origin,String name, Type type,ASTNode init) {
    DeclarationStatement res=new DeclarationStatement(name,type,init);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;    
  }
  public DeclarationStatement field_decl(E origin,String name, Type type,ASTNode init) {
    return field_decl(origin_source.create(origin),name,type,init);
  }
  public DeclarationStatement field_decl(String name, Type type,ASTNode init) {
    return field_decl(origin_stack.get(),name,type,init);
  }
  
  /**
   * Create a name expression that refers to a field name.
   */
  public NameExpression field_name(Origin origin,String name) {
    NameExpression res=new NameExpression(name);
    res.setKind(NameExpression.Kind.Field);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public NameExpression field_name(E origin,String name) {
    return field_name(origin_source.create(origin),name);
  }
  public NameExpression field_name(String name) {
    return field_name(origin_stack.get(),name);
  }
  
  /**
   * Create a name expression that refers to a label.
   */
  public NameExpression label(Origin origin,String name) {
    NameExpression res=new NameExpression(name);
    res.setKind(NameExpression.Kind.Label);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public NameExpression label(E origin,String name) {
    return label(origin_source.create(origin),name);
  }
  public NameExpression label(String name) {
    return label(origin_stack.get(),name);
  }
  
  /**
   * Create a name expression that refers to a local variable.
   */
  public NameExpression local_name(Origin origin,String name) {
    NameExpression res=new NameExpression(name);
    res.setKind(NameExpression.Kind.Local);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public NameExpression local_name(E origin,String name) {
    return local_name(origin_source.create(origin),name);
  }
  public NameExpression local_name(String name) {
    return local_name(origin_stack.get(),name);
  }

  /**
   * Create a name expression referring to an arbitrary name.
   */
  public NameExpression identifier(Origin origin,String name){
    NameExpression res=new NameExpression(name);
    res.setKind(NameExpression.Kind.Unresolved);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public NameExpression identifier(E origin,String name){
    return identifier(origin_source.create(origin),name);
  }
  public NameExpression identifier(String name) {
    return identifier(origin_stack.get(),name);
  }

  /**
   * Create an if-then-else statement.
   */
  public IfStatement ifthenelse(Origin origin,ASTNode test,ASTNode ... branches){
    if (branches.length<1 || branches.length>2 ) Abort("illegal number of branches");
    IfStatement res=new IfStatement();
    res.addClause(test,branches[0]);
    if (branches.length==2 && branches[1]!=null) res.addClause(IfStatement.else_guard,branches[1]);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;    
  }
  public IfStatement ifthenelse(E origin,ASTNode test,ASTNode ... branches){
    return ifthenelse(origin_source.create(origin),test,branches);
  }
  public IfStatement ifthenelse(ASTNode test,ASTNode ... branches){
    return ifthenelse(origin_stack.get(),test,branches);
  }

  /**
   * Create a new method invokation node.
   */
  public MethodInvokation invokation(Origin origin,ASTNode object,boolean guarded,NameExpression method,ASTNode ... args){
    MethodInvokation res=new MethodInvokation(object,guarded,method,args);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public MethodInvokation invokation(E origin,ASTNode object,boolean guarded,NameExpression method,ASTNode ... args){
    return invokation(origin_source.create(origin),object,guarded,method,args);
  }
  public MethodInvokation invokation(ASTNode object,boolean guarded,NameExpression method,ASTNode ... args){
    return invokation(origin_stack.get(),object,guarded,method,args);
  }
  
  
  /**
   * Create a method declaration
   */
  public Method method_kind(Origin origin,Method.Kind kind,Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    Method res=new Method(kind,name,returns,contract,args,body);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public Method method_kind(E origin,Method.Kind kind,Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    return method_kind(origin_source.create(origin),kind,returns,contract,name,args,body);
  }
  public Method method_kind(Method.Kind kind,Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    return method_kind(origin_stack.get(),kind,returns,contract,name,args,body);
  }
  
  /**
   * Create a method declaration
   */
  public Method method_decl(Origin origin,Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    Method res=new Method(Method.Kind.Plain,name,returns,contract,args,body);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public Method method_decl(E origin,Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    return method_decl(origin_source.create(origin),returns,contract,name,args,body);
  }
  public Method method_decl(Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    return method_decl(origin_stack.get(),returns,contract,name,args,body);
  }
  
  /**
   * Create a function declaration
   */
  public Method function_decl(Origin origin,Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    Method res=new Method(Method.Kind.Pure,name,returns,contract,args,body);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public Method function_decl(E origin,Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    return function_decl(origin_source.create(origin),returns,contract,name,args,body);
  }
  public Method function_decl(Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    return function_decl(origin_stack.get(),returns,contract,name,args,body);
  }
  

  /**
   * Create a name expression referring to a method name.
   */
  public NameExpression method_name(Origin origin,String name){
    NameExpression res=new NameExpression(name);
    res.setKind(NameExpression.Kind.Method);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public NameExpression method_name(E origin,String name){
    return method_name(origin_source.create(origin),name);
  }
  public NameExpression method_name(String name) {
    return method_name(origin_stack.get(),name);
  }

  /**
   * Create an instantiation of a new object.
   */
  public MethodInvokation new_object(Origin origin,Type type,ASTNode ... args){
    String name=null;
    if (type instanceof ClassType){
      name=((ClassType)type).getName();
    } else {
      Fail("cannot instantiate type %s",type);
    }
    return invokation(origin, type, false, method_name(origin,name) , args);
  }
  public MethodInvokation new_object(E origin,Type type,ASTNode ... args){
    return new_object(origin_source.create(origin),type,args); 
  }
  public MethodInvokation new_object(Type type,ASTNode ... args){
    return new_object(origin_stack.get(),type,args); 
  }
  
  /**
   * Create a predicate declaration.
   */
  public Method predicate(Origin origin, String name, ASTNode body,DeclarationStatement ... args) {
    Type bool=new PrimitiveType(Sort.Boolean);
    bool.setOrigin(origin);
    Method res=new Method(Method.Kind.Predicate, name, bool, null, args, body);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;    
  }
  public Method predicate(E origin,String name, ASTNode body, DeclarationStatement ... args) {
    return predicate(origin_source.create(origin),name,body,args);
  }
  public Method predicate(String name, ASTNode body, DeclarationStatement ... args) {
    return predicate(origin_stack.get(),name,body,args);
  }
  
  /**
   * Create a new primitive type.
   */
  public PrimitiveType primitive_type(Origin origin,PrimitiveType.Sort sort){
    PrimitiveType res=new PrimitiveType(sort);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;        
  }
  public PrimitiveType primitive_type(E origin,PrimitiveType.Sort sort){
    return primitive_type(origin_source.create(origin),sort);
  }
  public PrimitiveType primitive_type(PrimitiveType.Sort sort){
    return primitive_type(origin_stack.get(),sort);
  }
  
  /**
   * Create a new reserved name expression.
   * 
   * Reserved names are (for now) all reserved keywords:
   * this, super, null, \result, etc. To allow for future refactoring,
   * this method returns ASTNode on purpose. E.g. null might
   * yield a constant expression instead of a name expression.
   */
  public NameExpression reserved_name(Origin origin,String name){
    NameExpression res=new NameExpression(name);
    res.setKind(NameExpression.Kind.Reserved);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public NameExpression reserved_name(E origin,String name) {
    return reserved_name(origin_source.create(origin),name);
  }
  public NameExpression reserved_name(String name) {
    return reserved_name(origin_stack.get(),name);
  }

  /**
   * Create a new return statement.
   * @param value At most one node which is the returned value.
   */
  public ReturnStatement return_statement(Origin origin,ASTNode ... value){
    if (value.length>1) Abort("illegal number of return values");
    ReturnStatement res;
    if (value.length==0){
      res=new ReturnStatement();
    } else {
      res=new ReturnStatement(value[0]);
    }
    res.setOrigin(origin);
    res.accept_if(post);
    return res;    
  }
  public ReturnStatement return_statement(E origin,ASTNode ... value){
    return return_statement(origin_source.create(origin),value);
  }
  public ReturnStatement return_statement(ASTNode ... value){
    return return_statement(origin_stack.get(),value);
  }
  
  /**
   * Create an empty root package.
   */
  public ASTClass root_package(Origin origin){
    ASTClass res=new ASTClass();
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public ASTClass root_package(E origin){
    return root_package(origin_source.create(origin));
  }
  public ASTClass root_package(){
    return root_package(origin_stack.get());
  }
  
  /**
   * Create a sub-package.
   */
  public ASTClass sub_package(Origin origin,String name){
    return ast_class(name,ClassKind.Package,null,null);
  }
  public ASTClass sub_package(E origin,String name){
    return sub_package(origin_source.create(origin),name);
  }
  public ASTClass sub_package(String name){
    return sub_package(origin_stack.get(),name);
  }
  
  /**
   * Create a reserved name this that also refers to the given class type.
   */
  public ASTNode this_expression(Origin origin,ClassType t) {
    NameExpression res=new NameExpression("this");
    res.setType(t);
    res.setKind(NameExpression.Kind.Reserved);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public ASTNode this_expression(E origin,ClassType t) {
    return this_expression(origin_source.create(origin),t);
  }
  public ASTNode this_expression(ClassType t) {
    return this_expression(origin_stack.get(),t);
  }
   
  
  /**
   * Create a new while loop.
   */
  public LoopStatement while_loop(Origin origin,ASTNode test,ASTNode body,ASTNode ... invariant){
    LoopStatement res=new LoopStatement();
    res.setEntryGuard(test);
    res.setBody(body);
    res.setOrigin(origin);
    for (ASTNode inv:invariant) res.appendInvariant(inv);
    res.accept_if(post);
    return res;    
  }
  public LoopStatement while_loop(E origin,ASTNode test,ASTNode body,ASTNode ... invariant){
    return while_loop(origin_source.create(origin),test,body,invariant);
  }
  public LoopStatement while_loop(ASTNode test,ASTNode body,ASTNode ... invariant){
    return while_loop(origin_stack.get(),test,body,invariant);
  }
  
  
  /**
   * Create a new auxiliary with node.
   */
  public ASTNode with(Origin origin,String[] from, Kind kind, boolean all, ASTNode body) {
    // types are irrelevant for a with node.
    ASTNode res=new ASTWith(from,kind,all,body);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public ASTNode with(E origin,String[] from, Kind kind, boolean all, ASTNode body) {
    return with(origin_source.create(origin),from,kind,all,body);
  }
  public ASTNode with(String[] from, Kind kind, boolean all, ASTNode body) {
    return with(origin_stack.get(),from,kind,all,body);
  }

  /**
   * Create a new binding expression.
   */
  public ASTNode binder(Origin origin,Binder b,DeclarationStatement decls[],ASTNode selection,ASTNode main) {
    ASTNode res=new BindingExpression(b,decls,selection,main);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public ASTNode binder(E origin,Binder b,DeclarationStatement decls[],ASTNode selection,ASTNode main) {
    return binder(origin_source.create(origin),b,decls,selection,main);
  }
  public ASTNode binder(Binder b,DeclarationStatement decls[],ASTNode selection,ASTNode main) {
    return binder(origin_stack.get(),b,decls,selection,main);      
  }

  public void addRandomConstructor(ASTClass cl){
    enter();
    setOrigin(cl.getOrigin());
    ContractBuilder cb=new ContractBuilder();
    for(DeclarationStatement field : cl.dynamicFields()){
      cb.requires(expression(
          StandardOperator.Perm,
          field_name(field.getName()),
          constant(100)
      ));
      cb.ensures(expression(
          StandardOperator.Perm,
          field_name(field.getName()),
          constant(100)
     ));
    }
    Method cons=new Method(Method.Kind.Constructor, cl.getName(),primitive_type(PrimitiveType.Sort.Void), cb.getContract(), new DeclarationStatement[0],block());
    cons.setOrigin(cl.getOrigin());
    cl.add_dynamic(cons);
    leave();
  }

  public void addZeroConstructor(ASTClass cl){
    enter();
    setOrigin(cl.getOrigin());
    ContractBuilder cb=new ContractBuilder();
    BlockStatement body=block();
    for(DeclarationStatement field : cl.dynamicFields()){
      ASTNode zero=field.getType().zero();
      zero.setOrigin(cl.getOrigin());
      cb.ensures(expression(
           StandardOperator.PointsTo,
           field_name(field.getName()),
           constant(100),
           zero
      ));
      body.add_statement(assignment(field_name(field.getName()),zero));
    }
    Method cons=new Method(Method.Kind.Constructor, cl.getName(),primitive_type(PrimitiveType.Sort.Void), cb.getContract(), new DeclarationStatement[0],body);
    cons.setOrigin(cl.getOrigin());
    cl.add_dynamic(cons);
    leave();
  }

}
