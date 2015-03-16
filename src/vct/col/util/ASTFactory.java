// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.util;

import java.util.ArrayList;
import java.util.EnumSet;

import vct.col.ast.*;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTSpecialDeclaration.Kind;
import vct.col.ast.BindingExpression.Binder;
import vct.col.ast.PrimitiveType.Sort;
import vct.util.Configuration;
import hre.ast.Origin;
import hre.util.FrameControl;
import hre.util.FrameReference;
import static hre.System.*;
import static vct.col.ast.ASTReserved.Null;

/**
 * This class provides a factory for ASTNodes, that can be
 * configured to (semi-)automatically insert origins.
 * 
 * For every AST construction method, the newly created node will have the current
 * top of the origin stack as its origin.
 * 
 * To create an AST node with a specific origin, one can use chaining:
 * <pre>
  create.setOrigin(origin).expression(....)
 * </pre>
 * 
 * @author Stefan Blom
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
   * Create a new abstract class.
   */
  public ASTClass abstract_class(String name,ClassType super_class,ClassType ... supports) {
    ClassType bases[]={super_class};
    if (super_class==null) bases=null;
    return ast_class(name,ClassKind.Abstract,bases,supports);
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
    Method cons=method_kind(
        Method.Kind.Constructor,
        primitive_type(PrimitiveType.Sort.Void),
        cb.getContract(),
        cl.getName(),
        new DeclarationStatement[0],
        block()
    );
    cl.add_dynamic(cons);
    leave();
  }
 
  public ASTNode fullPermission(){
    return reserved_name(ASTReserved.FullPerm);
  }

  public void addZeroConstructor(ASTClass cl){
    enter();
    setOrigin(cl.getOrigin());
    ContractBuilder cb=new ContractBuilder();
    BlockStatement body=block();
    for(DeclarationStatement field : cl.dynamicFields()){
      ASTNode zero=field.getType().zero();
      if (zero!=null){
        zero.setOrigin(cl.getOrigin());
        cb.ensures(expression(
             StandardOperator.PointsTo,
             field_name(field.getName()),
             fullPermission(),
             zero
        ));
        body.add_statement(assignment(field_name(field.getName()),zero));
      } else {
        cb.ensures(expression(
            StandardOperator.Perm,
            field_name(field.getName()),
            fullPermission()
       ));       
      }
    }
    Method cons=method_kind(
        Method.Kind.Constructor,
        primitive_type(PrimitiveType.Sort.Void),
        cb.getContract(),
        cl.getName(),
        new DeclarationStatement[0],
        body);
    cl.add_dynamic(cons);
    leave();
  }
  
  /**
   * Create a name expression that refers to an argument variable.
   */
  public NameExpression argument_name(String name) {
    NameExpression res=new NameExpression(name);
    res.setKind(NameExpression.Kind.Argument);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }

  /**
   * Create an assignment statement/expression.
   */
  public ASTNode assignment(ASTNode loc, ASTNode val) {
    AssignmentStatement res=new AssignmentStatement(loc,val);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
  
  /**
   * Create a new class.
   */
  public ASTClass ast_class(String name,ClassKind kind,ClassType bases[],ClassType supports[]) {
    if (bases==null) bases=new ClassType[0];
    if (supports==null) supports=new ClassType[0];
    ASTClass res=new ASTClass(name,kind,bases,supports);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;    
  }
  
  public ParallelBarrier barrier(Contract c,EnumSet<ParallelBarrier.Fence> fences){
     return barrier(origin_stack.get(),c,fences);
   }
  
  public ParallelBarrier barrier(E origin,Contract c,EnumSet<ParallelBarrier.Fence> fences){
     return barrier(origin_source.create(origin),c,fences);
   }

  /**
    * Create a new barrier node.
    */
   public ParallelBarrier barrier(Origin origin,Contract c,EnumSet<ParallelBarrier.Fence> fences){
     ParallelBarrier res=new ParallelBarrier(c,fences);
     res.setOrigin(origin);
     res.accept_if(post);
     return res;
   }

  /**
   * Create a new binding expression.
   */
  public ASTNode binder(Binder b,Type result_type,DeclarationStatement decls[],ASTNode selection,ASTNode main) {
    ASTNode res=new BindingExpression(b,result_type,decls,selection,main);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
  /**
   * Create a new block, with the given statements as (initial) contents.
   */
  public BlockStatement block(ASTNode ... args) {
    return block(origin_stack.get(),args);        
  }

public BlockStatement block(Origin origin, ASTNode ... args) {
  BlockStatement res=new BlockStatement();
  for(ASTNode node:args){
    res.add_statement(node);
  }
  res.setOrigin(origin);
  res.accept_if(post);
  return res;        
}


  public ClassType class_type(E origin,String name[],ASTNode ... args){
    return class_type(origin_source.create(origin),name,args);
  }
  public ClassType class_type(E origin,String name,ASTNode ... args){
    return class_type(origin_source.create(origin),name,args);
  }
  /**
   * Create a new class type node.
   */
  public ClassType class_type(Origin origin,String name[],ASTNode ... args){
    ClassType res=new ClassType(name,args);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;
  }
  public ClassType class_type(Origin origin,String name,ASTNode ... args){
    String tmp[]=new String[1];
    tmp[0]=name;
    return class_type(origin,tmp,args);
  }

  
  public ClassType class_type(String name[],ASTNode ... args){
    return class_type(origin_stack.get(),name,args);
  }
  public ClassType class_type(String name,ASTNode ... args){
    return class_type(origin_stack.get(),name,args);
  }
  public ASTSpecialDeclaration comment(String text) {
    return special_decl(vct.col.ast.ASTSpecialDeclaration.Kind.Comment,constant(text));
  }

  public ConstantExpression constant(boolean b) {
    return constant(origin_stack.get(),b);
  }
  public ConstantExpression constant(double i) {
    return constant(origin_stack.get(),i);
  }
  public ConstantExpression constant(E origin,boolean b) {
    return constant(origin_source.create(origin),b);
  }
  
  public ConstantExpression constant(E origin,double i) {
    return constant(origin_source.create(origin),i);
  }
  public ConstantExpression constant(E origin,int i) {
    return constant(origin_source.create(origin),i);
  }
  public ConstantExpression constant(E origin,long i) {
    return constant(origin_source.create(origin),i);
  }
  
  public ConstantExpression constant(E origin,String s) {
    return constant(origin_source.create(origin),s);
  }
  public ConstantExpression constant(int i) {
    return constant(origin_stack.get(),i);
  }
  public ConstantExpression constant(long i) {
    return constant(origin_stack.get(),i);
  }
  /**
   * Create a new boolean constant.
   */
  public ConstantExpression constant(Origin origin, boolean b) {
    ConstantExpression res=new ConstantExpression(b,origin);
    res.accept_if(post);
    return res;    
  }
  /**
   * Create a new double constant.
   */
  public ConstantExpression constant(Origin origin, double i) {
    ConstantExpression res=new ConstantExpression(i,origin);
    res.accept_if(post);
    return res;    
  }
  /**
   * Create a new integer constant.
   */
  public ConstantExpression constant(Origin origin, int i) {
    ConstantExpression res=new ConstantExpression(i,origin);
    res.accept_if(post);
    return res;    
  }

  /**
   * Create a new long constant.
   */
  public ConstantExpression constant(Origin origin, long i) {
    ConstantExpression res=new ConstantExpression(i,origin);
    res.accept_if(post);
    return res;    
  }
  /**
   * Create a new string constant.
   */
  public ConstantExpression constant(Origin origin, String s) {
    ConstantExpression res=new ConstantExpression(s,origin);
    res.accept_if(post);
    return res;    
  }
  public ConstantExpression constant(String s) {
    return constant(origin_stack.get(),s);
  }
  
   
  /** Create a dereference expression.
   */
  public Dereference dereference(ASTNode object,String field){
    Dereference res=new Dereference(object,field);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
  
  /**
   * Enter a new stack frame of the origin stack.
   */
  public void enter(){
    origin_stack.enter();
  }
  
  public OperatorExpression expression(E origin,StandardOperator op, ASTNode ... args){
    return expression(origin_source.create(origin),op,args);
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
  
  public OperatorExpression expression(StandardOperator op, ASTNode ... args){
    return expression(origin_stack.get(),op,args);
  }
  /**
   * Create a new variable declaration with default value.
   * 
   * Used for members, arguments and local variables.
   * 
   * @param name The name of the variable.
   * @param type The type of the variable.
   * @param init The optional initial value of the variable.
   * @return An AST node containing the variable declaration.
   */
  public DeclarationStatement field_decl(String name, Type type,ASTNode ... init) {
    if (type.isNull()){
      Abort("cannot declare variable %s of <<null>> type.",name);
    }
    if (init !=null && init.length>1) Abort("cannot have more than one initial value.");
    DeclarationStatement res=new DeclarationStatement(name,type,init==null?null:init.length==0?null:init[0]);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;    
  }
  
  /**
   * Create a name expression that refers to a field name.
   */
  public NameExpression field_name(String name) {
    NameExpression res=new NameExpression(name);
    res.setKind(NameExpression.Kind.Field);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }

  /**
   * Fold left of a non-empty list. 
   * 
   * @param op Operator to fold with.
   * @param list Non-empty list of terms.
   * @return folded list.
   */
   public ASTNode fold(StandardOperator op, ArrayList<ASTNode> list) {
     if (list.size()==0){
       switch(op){
       case And:
       case Star:
         return constant(true);
       default:
         Abort("cannot fold empty list, because neutral element of %s is not implemented",op);
       }
     }
     ASTNode res=list.get(0);
     int N=list.size();
     for(int i=1;i<N;i++){
       res=expression(op,res,list.get(i));
     }
     return res;
   }
   
   /**
    * Fold left of a non-empty list. 
    * 
    * @param op Operator to fold with.
    * @param list Non-empty list of terms.
    * @return folded list.
    */
    public ASTNode fold(StandardOperator op, ASTNode ... list) {
      if (list.length==0){
        switch(op){
        case And:
        case Star:
          return constant(true);
        default:
          Abort("cannot fold empty list, because neutral element of %s is not implemented",op);
        }
      }
      ASTNode res=list[0];
      int N=list.length;
      for(int i=1;i<N;i++){
        res=expression(op,res,list[i]);
      }
      return res;
    }

    public LoopStatement for_loop(ASTNode init, ASTNode test, ASTNode update, ASTNode body,ASTNode ... invariant){
      LoopStatement res=new LoopStatement();
      res.setEntryGuard(test);
      res.setInitBlock(init);
      res.setUpdateBlock(update);
      res.setBody(body);
      res.setOrigin(origin_stack.get());
      for (ASTNode inv:invariant) res.appendInvariant(inv);
      res.fixate();
      res.accept_if(post);
      return res;    
    }
          
    public LoopStatement for_loop(ASTNode init, ASTNode test, ASTNode update, ASTNode body,Contract contract){
      LoopStatement res=new LoopStatement();
      res.setEntryGuard(test);
      res.setInitBlock(init);
      res.setUpdateBlock(update);
      res.setBody(body);
      res.setOrigin(origin_stack.get());
      res.setContract(contract);
      res.accept_if(post);
      return res;    
    }
          
    public BindingExpression exists(ASTNode guard, ASTNode claim, DeclarationStatement ... decl) {
      BindingExpression res=new BindingExpression(
          Binder.EXISTS,
          primitive_type(PrimitiveType.Sort.Boolean),
          decl,
          guard,
          claim
      );
      res.setOrigin(origin_stack.get());
      res.accept_if(post);
      return res;
    }
    public BindingExpression summation(ASTNode guard, ASTNode claim, DeclarationStatement ... decl) {
      int i=decl.length-1;
      BindingExpression res=new BindingExpression(
          Binder.SUM,
          null,
          new DeclarationStatement[]{decl[i]},
          guard,
          claim
      );
      res.setOrigin(origin_stack.get());
      res.accept_if(post);
      while(i>0){
        i--;
        res=new BindingExpression(
            Binder.SUM,
            null,
            new DeclarationStatement[]{decl[i]},
            constant(true),
            res
        );
        res.setOrigin(origin_stack.get());
        res.accept_if(post);
      }
      return res;
    }
  public BindingExpression let_expr(DeclarationStatement decl,ASTNode in) {
    BindingExpression res=new BindingExpression(
        Binder.LET,
        null,
        new DeclarationStatement[]{decl},
        null,
        in
    );
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }

  /**
   * Create a function declaration
   */
  public Method function_decl(Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    return method_kind(Method.Kind.Pure,returns,contract,name,args,false,body);
  }
  
  /**
   * Get the current origin. 
   */
  public Origin getOrigin() {
    return origin_stack.get();
  }
  /**
   * Create a name expression referring to an arbitrary name.
   */
  public NameExpression identifier(String name){
    NameExpression res=new NameExpression(name);
    res.setKind(NameExpression.Kind.Unresolved);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
  
  /**
   * Create an if-then-else statement.
   */
  public IfStatement ifthenelse(ASTNode test,ASTNode ... branches){
    if (branches.length<1 || branches.length>2 ) Abort("illegal number of branches");
    IfStatement res=new IfStatement();
    res.addClause(test,branches[0]);
    if (branches.length==2 && branches[1]!=null) res.addClause(IfStatement.else_guard,branches[1]);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;    
  }
  
  /**
   * Create a new method invokation node.
   */
  public MethodInvokation invokation(ASTNode object,ClassType dispatch,String method,ASTNode ... args){
    MethodInvokation res=new MethodInvokation(object,dispatch,method,args);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }

  /**
   * Create a name expression that refers to a label.
   */
  public NameExpression label(String name) {
    NameExpression res=new NameExpression(name);
    res.setKind(NameExpression.Kind.Label);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
  /**
   * Leave the current stack frame of the origin stack.
   */
  public void leave(){
    origin_stack.leave();
  }
  public ASTNode lemma(vct.col.ast.BlockStatement block) {
    ASTNode res=new Lemma(block);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }

  /**
   * Create a name expression that refers to a local variable.
   */
  public NameExpression local_name(String name) {
    NameExpression res=new NameExpression(name);
    res.setKind(NameExpression.Kind.Local);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }

  /**
   * Create a method declaration
   */
  public Method method_decl(Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    return method_kind(Method.Kind.Plain,returns,contract,name,args,false,body);
  }
  
  /**
   * Create a method declaration
   */
  public Method method_kind(Method.Kind kind,Type returns,Contract contract,String name,DeclarationStatement args[],ASTNode body){
    return method_kind(kind,returns,contract,name,args,false,body);
  }
  /**
   * Create a method declaration
   */
  public Method method_kind(Method.Kind kind,Type returns,Contract contract,String name,DeclarationStatement args[],boolean varArgs,ASTNode body){
    Method res=new Method(kind,name,returns,contract,args,varArgs,body);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
  public NameExpression method_name(E origin,String name){
    return method_name(origin_source.create(origin),name);
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
  public NameExpression method_name(String name) {
    return method_name(origin_stack.get(),name);
  }

  /**
   * Create a name expression that refers to a specific kind.
   */
  public NameExpression name(NameExpression.Kind kind,ASTReserved word,String name) {
    NameExpression res=new NameExpression(kind,word,name);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }

  /**
   * Create a new plain class.
   */
  public ASTClass new_class(String name,ClassType super_class,ClassType ... supports) {
    ClassType bases[]={super_class};
    if (super_class==null) bases=null;
    return ast_class(name,ClassKind.Plain,bases,supports);
  }
   
  
  /**
   * Create an instantiation of a new object.
   */
  public MethodInvokation new_object(Type type,ASTNode ... args){
    String name=null;
    if (type instanceof ClassType){
      name=((ClassType)type).getName();
    } else {
      Fail("cannot instantiate type %s",type);
    }
    return invokation(type, null, name , args);
  }
  
  /**
   * Construct a non_null expression.
   * 
   * @param expr Expression that is supposed to be non-null.
   * @return AST for <code> expr != null </code>
   */
  public ASTNode non_null(ASTNode expr) {
    return expression(StandardOperator.NEQ,expr,reserved_name(Null));
  }
  
  /**
   * Construct a non_null expression for a variable name.
   */
 public ASTNode non_null(String string) {
    return non_null(unresolved_name(string));
  }

  public ParallelBlock parallel_block(Contract c,DeclarationStatement name,ASTNode count,BlockStatement block){
     return parallel_block(origin_stack.get(),c, name, count, block);
   }

  public ParallelBlock parallel_block(E origin,Contract c,DeclarationStatement name,ASTNode count,BlockStatement block){
     return parallel_block(origin_source.create(origin),c, name, count, block);
   }

  /**
    * Create a new parallel block.
    */
   public ParallelBlock parallel_block(Origin origin,Contract contract,DeclarationStatement name,ASTNode count,BlockStatement block){
     ParallelBlock res=new ParallelBlock(contract, name, count, block);
     res.setOrigin(origin);
     res.accept_if(post);
     return res;
   }

  /**
   * Create a predicate declaration.
   */
  public Method predicate(String name, ASTNode body,DeclarationStatement ... args) {
    return method_kind(Method.Kind.Predicate,primitive_type(Sort.Resource),null,name,args,false,body);
  } 
  
  public PrimitiveType primitive_type(E origin,PrimitiveType.Sort sort,ASTNode ... args){
    return primitive_type(origin_source.create(origin),sort,args);
  }
  
  /**
   * Create a new primitive type.
   */
  public PrimitiveType primitive_type(Origin origin,PrimitiveType.Sort sort,ASTNode ... args){
    PrimitiveType res=new PrimitiveType(sort,args);
    res.setOrigin(origin);
    res.accept_if(post);
    return res;        
  }

 public PrimitiveType primitive_type(PrimitiveType.Sort sort,ASTNode ... args){
  return primitive_type(origin_stack.get(),sort,args);
}

  /**
   * Create a new reserved name expression.
   * 
   * Reserved names are (for now) all reserved keywords:
   * this, super, null, \result, etc. To allow for future refactoring,
   * this method returns ASTNode on purpose. E.g. null might
   * yield a constant expression instead of a name expression.
   */
  public NameExpression reserved_name(ASTReserved name){
    NameExpression res=new NameExpression(name);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
  
  /**
   * Create a new reserved name expression with a fixed type.
   *
   * Added to experiment with kernels, may not become permanent.
   */
  public NameExpression reserved_name(ASTReserved name,Type t){
    NameExpression res=new NameExpression(name);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    res.setType(t);
    return res;
  }
 
 
 /**
 * Create a new return statement.
 * @param value At most one node which is the returned value.
 */
public ReturnStatement return_statement(ASTNode ... value){
  if (value.length>1) Abort("illegal number of return values");
  ReturnStatement res;
  if (value.length==0){
    res=new ReturnStatement();
  } else {
    res=new ReturnStatement(value[0]);
  }
  res.setOrigin(origin_stack.get());
  res.accept_if(post);
  return res;    
}
 /**
 * Replace the current origin.
 * 
 * This method returns the AST to allow chaining.
 * 
 * @param origin The new origin.
 * @return The AST factory.
 */
public ASTFactory setOrigin(Origin origin) {
  this.origin_stack.set(origin);
  return this;
}
public ASTSpecial special(Origin origin, vct.col.ast.ASTSpecial.Kind kind, ASTNode ... args) {
  ASTSpecial res=new ASTSpecial(kind,args);
  res.setOrigin(origin);
  res.accept_if(post);
  return res;
}
 public ASTSpecial special(vct.col.ast.ASTSpecial.Kind kind, ASTNode ... args) {
  return special(origin_stack.get(),kind,args);
}
 public ASTSpecialDeclaration special_decl(Origin origin, vct.col.ast.ASTSpecialDeclaration.Kind kind, ASTNode ... args) {
   ASTSpecialDeclaration res=new ASTSpecialDeclaration(kind,args);
   res.setOrigin(origin);
   res.accept_if(post);
   return res;
 }
  public ASTSpecialDeclaration special_decl(vct.col.ast.ASTSpecialDeclaration.Kind kind, ASTNode ... args) {
   return special_decl(origin_stack.get(),kind,args);
 }

  public BindingExpression starall(ASTNode guard, ASTNode claim, DeclarationStatement ... decl) {
    int i=decl.length-1;
    BindingExpression res=new BindingExpression(
        Binder.STAR,
        primitive_type(PrimitiveType.Sort.Resource),
        new DeclarationStatement[]{decl[i]},
        guard,
        claim
    );
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    while(i>0){
      i--;
      res=new BindingExpression(
          Binder.STAR,
          primitive_type(PrimitiveType.Sort.Resource),
          new DeclarationStatement[]{decl[i]},
          constant(true),
          res
      );
      res.setOrigin(origin_stack.get());
      res.accept_if(post);
    }
    return res;
  }
  public BindingExpression forall(ASTNode guard, ASTNode claim, DeclarationStatement ... decl) {
    int i=decl.length-1;
    BindingExpression res=new BindingExpression(
        Binder.FORALL,
        primitive_type(PrimitiveType.Sort.Boolean),
        new DeclarationStatement[]{decl[i]},
        guard,
        claim
    );
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    while(i>0){
      i--;
      res=new BindingExpression(
          Binder.FORALL,
          primitive_type(PrimitiveType.Sort.Boolean),
          new DeclarationStatement[]{decl[i]},
          constant(true),
          res
      );
      res.setOrigin(origin_stack.get());
      res.accept_if(post);
    }
    return res;
  }
 /**
 * Create a reserved name this that also refers to the given class type.
 */
public ASTNode this_expression(ClassType t) {
  NameExpression res=new NameExpression(ASTReserved.This);
  res.setType(t);
  res.setOrigin(origin_stack.get());
  res.accept_if(post);
  return res;
}

/**
 * Create a name expression that refers to an unresolved name.
 */
public NameExpression unresolved_name(String name) {
  NameExpression res=new NameExpression(name);
  res.setKind(NameExpression.Kind.Unresolved);
  res.setOrigin(origin_stack.get());
  res.accept_if(post);
  return res;
}

public VariableDeclaration variable_decl(Type type) {
  VariableDeclaration res=new VariableDeclaration(type);
  res.setOrigin(origin_stack.get());
  res.accept_if(post);
  return res;
}

/**
 * Create a new while loop.
 */
public LoopStatement while_loop(ASTNode test,ASTNode body,ASTNode ... invariant){
  LoopStatement res=new LoopStatement();
  res.setEntryGuard(test);
  res.setBody(body);
  res.setOrigin(origin_stack.get());
  for (ASTNode inv:invariant) res.appendInvariant(inv);
  res.fixate();
  res.accept_if(post);
  return res;    
}

/**
 * Create a new while loop.
 */
public LoopStatement while_loop(ASTNode test,ASTNode body,Contract contract){
  LoopStatement res=new LoopStatement();
  res.setEntryGuard(test);
  res.setBody(body);
  res.setOrigin(origin_stack.get());
  res.setContract(contract);
  res.accept_if(post);
  return res;    
}

/**
 * Create a new auxiliary with node.
 */
public ASTNode with(String[] from, ASTWith.Kind kind, boolean all, ASTNode body) {
  // types are irrelevant for a with node.
  ASTNode res=new ASTWith(from,kind,all,body);
  res.setOrigin(origin_stack.get());
  res.accept_if(post);
  return res;
}

public Type arrow_type(Type src, Type tgt) {
  Type res=new FunctionType(new Type[]{src},tgt);
  res.setOrigin(origin_stack.get());
  res.accept_if(post);
  return res;
}

public Type tuple_type(Type ... t) {
  Type res=new TupleType(t);
  res.setOrigin(origin_stack.get());
  res.accept_if(post);
  return res;
}

public Type arrow_type(Type[] types, Type tgt) {
  Type res=new FunctionType(types,tgt);
  res.setOrigin(origin_stack.get());
  res.accept_if(post);
  return res;
}

public ASTNode new_array(Type t, ASTNode size) {
  return expression(StandardOperator.NewArray,t,size);
}

public AxiomaticDataType adt(String name,DeclarationStatement ... pars) {
  AxiomaticDataType res=new AxiomaticDataType(name,pars);
  res.setOrigin(origin_stack.get());
  res.accept_if(post);
  return res;
}

public Axiom axiom(String name,ASTNode exp){
  Axiom res=new Axiom(name,exp);
  res.setOrigin(origin_stack.get());
  res.accept_if(post);
  return res;
}

  public ASTNode expression(StandardOperator op, ASTNode arg0, ASTNode [] args){
    ASTNode all_args[]=new ASTNode[args.length+1];
    all_args[0]=arg0;
    for(int i=0;i<args.length;i++){
      all_args[i+1]=args[i];
    }
    return expression(op,all_args);
  }
  
  public ActionBlock action_block(ASTNode process,ASTNode action, ASTNode block) {
    ActionBlock res=new ActionBlock(process,action,block);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }

  public Type __const(Type type) {
    Type res=new TypeExpression(TypeOperator.Const,type);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
  public Type __short(Type type) {
    Type res=new TypeExpression(TypeOperator.Short,type);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
  public Type __signed(Type type) {
    Type res=new TypeExpression(TypeOperator.Signed,type);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
  public Type __unsigned(Type type) {
    Type res=new TypeExpression(TypeOperator.Unsigned,type);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
  public Type __long(Type type) {
    Type res=new TypeExpression(TypeOperator.Long,type);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }

  public ForEachLoop foreach(DeclarationStatement[] decls,ASTNode guard, ASTNode body) {
    ForEachLoop res=new ForEachLoop(decls,guard,body);
    res.setOrigin(origin_stack.get());
    res.accept_if(post);
    return res;
  }
}
