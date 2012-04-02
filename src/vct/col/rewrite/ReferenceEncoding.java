package vct.col.rewrite;

import hre.ast.MessageOrigin;
import hre.ast.Origin;

import java.util.ArrayList;
import java.util.HashMap;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTVisitor;
import vct.col.ast.BlockStatement;
import vct.col.ast.MethodInvokation;
import vct.col.ast.ClassType;
import vct.col.ast.ConstantExpression;
import vct.col.ast.Contract;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.FunctionType;
import vct.col.ast.IfStatement;
import vct.col.ast.Method;
import vct.col.ast.Method.Kind;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import static hre.System.Abort;

/**
 * This rewriter builds the reference encoding of the given program.
 * 
 * @author sccblom
 *
 */
public class ReferenceEncoding extends AbstractRewriter {

  /**
   * Add a suffix to the last part of a composite name.
   * @param name composite name
   * @param suffix suffix for last part
   * @return A copy of the name with the suffix added.
   */
  public static String[] append_suffix(final String name[],final String suffix){
    String res[]=new String[name.length];
    for(int i=0;i<name.length-1;i++){
      res[i]=name[i];
    }
    res[name.length-1]=name[name.length-1]+suffix;
    return res;
  }

  /** The following rewriter copies the AST it is applied to.
   *  This is necessary to ensure that the AST returned is completely
   *  disjoint from the AST the main rewriter was applied to.
   */
  private AbstractRewriter copy_rw=new AbstractRewriter(){};

  /** This rewriter is applied to a class to generate the data part
   *  of the reference encoding.
   */
  private AbstractRewriter data_rw=new AbstractRewriter(){
    /**
     * Main method for the class.
     * 
     * By calling convention, this method is the entry point.
     * It will scan the given class and build the corresponding data class.
     */
    private boolean active=false;
    public void visit(ASTClass c) {
      if (active) {
        Abort("nested class");
      }
      active=true;
      String name=c.getName();
      if (c.getStaticCount()>0) throw new Error("class "+name+" has static content, which is future work");
      ASTClass res=new ASTClass(name+"_data",ClassKind.Plain);
      res.setOrigin(c.getOrigin());
      int M=c.getDynamicCount();
      for(int i=0;i<M;i++){
        ASTNode node=c.getDynamic(i);
        if (node instanceof DeclarationStatement){
          // Field members are copied.
          res.add_dynamic(node.apply(this));
        }
        // Other members are ignored.
      }
      active=false;
      result=res;
    }
    /**
     * Copy a field declaration with all types changed to _data.
     * At the same time put the name of the field into the local map.
     */
    public void visit(DeclarationStatement s) {
      Type t=s.getType();
      if (t instanceof ClassType) {
        ClassType ct=(ClassType)t;
        t=create.class_type(t.getOrigin(),append_suffix(ct.name,"_data"));
      } else {
        t=this.rewrite_and_cast(t);
      }
      String name=s.getName();
      local_map.put(name,t);
      ASTNode init=s.getInit();
      if (init!=null) {
        Abort("Reference encoding does not support initial expressions.");
        // init=init.apply(this);
      }
      DeclarationStatement res=new DeclarationStatement(name,t,init);
      res.setOrigin(s.getOrigin());
      result=res;
    }
  };
  
  /** This rewriter transforms clauses to the reference encoding format. */
  private AbstractRewriter clause_rw=new AbstractRewriter(){
    
    /**
     * this function should be at the top level, which requries that
     * all rewriters in the reference encoding use the same factory!
     */
    private ASTNode insert_ref(ASTNode expr){
      if (!(expr instanceof OperatorExpression)) Abort("cannot insert ref in %s",expr.getClass());
      OperatorExpression e=(OperatorExpression)expr;
      StandardOperator op=e.getOperator();
      if (op != StandardOperator.Select) Abort("cannot insert ref in %s expression",op);
      ASTNode name=e.getArg(1);
      ASTNode main=e.getArg(0);
      ASTNode ref=create.field_name("ref"); // TODO: check origin!
      main=create.expression(StandardOperator.Select,main,ref);
      return create.expression(StandardOperator.Select,main,name);
    }

    @Override
    /**
     * Translate predicates.
     */
    public void visit(MethodInvokation e) {
      // TODO: check if this method is a predicate and just copy if it is not.
      ASTNode object=rewrite_nullable(e.object);
      NameExpression pred=e.method;
      String name=pred.getName();
      NameExpression tmp;
      
      // First, we create a call to the generated valid predicate.
      tmp=new NameExpression(name+"_valid");
      tmp.setOrigin(pred.getOrigin());
      MethodInvokation valid=new MethodInvokation(object,e.guarded,tmp,new ASTNode[0]);
      valid.setOrigin(e.getOrigin());
      
      // Second, we create a call to the parameter checking function.
      int N=e.getArity();
      ASTNode args[]=new ASTNode[N];
      for(int i=0;i<N;i++){
        args[i]=e.getArg(i);
      }
      tmp=new NameExpression(name+"_check");
      tmp.setOrigin(pred.getOrigin());
      MethodInvokation check=new MethodInvokation(object,e.guarded,tmp,args);
      check.setOrigin(e.getOrigin());
      
      // We return the star conjunction of the two checks.
      OperatorExpression res=new OperatorExpression(StandardOperator.Star,valid,check);
      res.setOrigin(e.getOrigin());
      result=res;
    }
    
    public void visit(OperatorExpression e){
      if (e.getType()==null) Abort("untyped operator %s in clause at %s",e.getOperator(),e.getOrigin());
      switch(e.getOperator()){
      case Select:
        super.visit(e);
        System.err.printf("select %s of type %s at %s%n",((NameExpression)e.getArg(1)).getName(),e.getType(),e.getOrigin());
        if (!(e.getType() instanceof ClassType)){
          
          result=insert_ref(result);
        }
        return;
      default:
        super.visit(e);
        return;
      }
    }
  };

  /** This rewriter generates the reference part of the encoding of a
   *  given class.
   */
  private ASTVisitor<ASTNode> reference_rw=new AbstractRewriter(){

    /**
     * Default origin for generated code.
     */
    private Origin generated=new MessageOrigin("generated during reference encoding");

    /**
     * Type of a *_valid predicate. 
     */
    private FunctionType valid_type;
    {
      PrimitiveType bool_type=new PrimitiveType(Sort.Boolean);
      bool_type.setOrigin(generated);
      valid_type=new FunctionType(new Type[0],bool_type);
      valid_type.setOrigin(generated);
    }
    /**
     * Zero for use in permission range.
     */
    private ConstantExpression zero_permission;
    {
      zero_permission=new ConstantExpression(0);
      zero_permission.setOrigin(generated);
    }
    
    /**
     * Maximum permission.
     * 
     * TODO: make this configurable instead of hard coded at 100.
     */
    private ConstantExpression full_permission;
    {
      full_permission=new ConstantExpression(100);
      full_permission.setOrigin(generated);
    }

    /**
     * Copy object on which the method is invoked and translate the arguments.
     * This assume that methods are invoked on fields and not on expressions.
     */
    public void visit(MethodInvokation e) {
      if (e.guarded) throw new Error("guarded invokation in plain code");
      if (e.object==null) Abort("unexpected null object");
      // copy the object on which the method is invoked:
      ASTNode object=e.object.apply(copy_rw);
      NameExpression method=e.method;
      // rewrite the arguments of the method:
      ASTNode args[]=e.map_args(this,new ASTNode[0]);
      // build new call.
      MethodInvokation res=new MethodInvokation(object,method,args);
      res.setOrigin(e.getOrigin());
      result=res;
    }

    private ASTNode field_permission(ClassType type,ASTNode name,ASTNode perm){
      ASTNode _this=create.this_expression(generated,type);
      ASTNode field=create.expression(generated,StandardOperator.Select,_this,name);
      return create.expression(generated,StandardOperator.Perm,field,perm);
    }
    
    public void visit(ASTClass c) {
      if (c.isPackage()) Abort("cannot create reference class for package");
      String name=c.getName();
      if (c.getStaticCount()>0) throw new Error("class "+name+" has static content");
      
      ASTClass res=create.ast_class(name+"_ref",ClassKind.Plain);
      ClassType data_type=create.class_type(append_suffix(c.getFullName(),"_data"));
      ClassType ref_type=create.class_type(append_suffix(c.getFullName(),"_ref"));
      
      // The ref field points to the data part. 
      
      res.add_dynamic(create.field_decl("ref",data_type));
      
      //// emit the valid ref predicate.
      // res.add_dynamic(create.predicate("valid_ref",valid_ref));
      
      
      int M=c.getDynamicCount();
      ArrayList<Method> predicates=new ArrayList<Method>();
      
      ASTNode valid_base=field_permission(ref_type,create.field_name(generated,"ref"),full_permission);
      ASTNode simple_base=IfStatement.else_guard;
      
      for(int i=0;i<M;i++){
        ASTNode node=c.getDynamic(i);
        if (node instanceof DeclarationStatement){
          DeclarationStatement decl=(DeclarationStatement)node;
          Origin o=decl.getOrigin();
          Type t=decl.getType();
          if (t instanceof ClassType){
            ClassType ct=(ClassType)t;
            ClassType ref_ct=create.class_type(o,append_suffix(ct.name,"_ref"));
            decl=create.field_decl(o,decl.getName(),ref_ct);
            res.add_dynamic(decl);
            ASTNode decl_name=new NameExpression(decl.getName());
            decl_name.setOrigin(generated);
            ASTNode decl_perm=new OperatorExpression(StandardOperator.Perm,decl_name,full_permission);
            decl_perm.setOrigin(generated);
            valid_base=new OperatorExpression(StandardOperator.Star,valid_base,decl_perm);
            valid_base.setOrigin(generated);  
          } else {
            System.err.printf("skipping type %s\n",node.getClass());
          }
        } else if (node instanceof Method) {
          Method m=(Method)node;
          if (m.getKind()==Kind.Predicate) {
            String method_name=m.getName();
            FunctionType t=m.getType();
            int N=m.getArity();
            String args[]=new String[N];
            for(int j=0;j<N;j++){
              args[j]=m.getArgument(j);
              DeclarationStatement decl=new DeclarationStatement(method_name+"_"+m.getArgument(j),t.getArgument(j));
              decl.setOrigin(generated);
              res.add_dynamic(decl);
              ASTNode decl_name=new NameExpression(method_name+"_"+m.getArgument(j));
              decl_name.setOrigin(generated);
              ASTNode decl_perm=new OperatorExpression(StandardOperator.Perm,decl_name,full_permission);
              decl_perm.setOrigin(generated);
              valid_base=new OperatorExpression(StandardOperator.Star,valid_base,decl_perm);
              valid_base.setOrigin(generated);
              simple_base=new OperatorExpression(StandardOperator.Star,simple_base,decl_perm);
              simple_base.setOrigin(generated);
              ASTNode low=new OperatorExpression(StandardOperator.LT,zero_permission,decl_name);
              low.setOrigin(generated);
              valid_base=new OperatorExpression(StandardOperator.Star,valid_base,low);
              valid_base.setOrigin(generated);
              ASTNode high=new OperatorExpression(StandardOperator.LTE,decl_name,full_permission);
              high.setOrigin(generated);
              valid_base=new OperatorExpression(StandardOperator.Star,valid_base,high);
              valid_base.setOrigin(generated);
            }
            predicates.add(m);
          } else {
            res.add_dynamic(node.apply(this));
          }
        } else {
          res.add_dynamic(node.apply(this));
        }
      }
      ASTNode _this=create.this_expression(generated,ref_type);
      ASTNode valid_body=valid_base;
      
      NameExpression valid_name=new NameExpression("valid");
      valid_name.setOrigin(generated);
      
      for (Method m:predicates){
        String method_name=m.getName();
        FunctionType t=m.getType();
        int N=m.getArity();
        Type type_args[]=new Type[N];
        String args[]=new String[N];
        ASTNode check_body=IfStatement.else_guard;
        BlockStatement setargs_body=create.block(generated);
        BlockStatement unfold_body=create.block(generated);
        BlockStatement fold_body=create.block(generated);
        for(int j=0;j<N;j++){
          type_args[j]=(Type)t.getArgument(j).apply(copy_rw);
          args[j]=m.getArgument(j);
          ASTNode arg_name=new NameExpression(m.getArgument(j));
          arg_name.setOrigin(generated);
          ASTNode var_name=new NameExpression(method_name+"_"+m.getArgument(j));
          var_name.setOrigin(generated);
          ASTNode test=new OperatorExpression(StandardOperator.EQ,arg_name,var_name);
          test.setOrigin(generated);
          if (check_body==IfStatement.else_guard){
            check_body=test;
          } else {
            check_body=new OperatorExpression(StandardOperator.And,check_body,test);
            check_body.setOrigin(generated);
          }
          setargs_body.add_statement(create.assignment(generated,var_name,arg_name));
        }
        //Method valid=new Method(Kind.Predicate,method_name+"_valid",new String[0],valid_type);
        ASTNode body=m.getBody();
        predicate=method_name;
        body=body.apply(valid_rw);
        //System.err.println("");
        //body=new OperatorExpression(StandardOperator.Star,valid_base,body);
        //body.setOrigin(m.getBody().getOrigin());
        //valid.setBody(body);
        //valid.setOrigin(m.getOrigin());
        //res.add_dynamic(valid);        
        
        // append predicate body to valid body.
        valid_body=create.expression(generated,StandardOperator.Star,valid_body,body);
        
        
        // emit ???_check function
        ASTNode check_maintained=new MethodInvokation(null,valid_name);
        check_maintained.setOrigin(generated);
        Method check=new Method(Kind.Pure,method_name+"_check",args,t);
        check.setBody(check_body);
        check.setContract(new Contract(check_maintained,check_maintained));
        check.setOrigin(m.getOrigin());
        res.add_dynamic(check);
        
        // create void(args) type.
        Type void_type=new PrimitiveType(PrimitiveType.Sort.Void);
        void_type.setOrigin(m.getOrigin());
        FunctionType tv=new FunctionType(type_args, void_type);
        tv.setOrigin(m.getOrigin());
        
        // // generate setargs method.
        //Method setargs=new Method(Kind.Plain,method_name+"_setargs",args,tv);
        //setargs.setBody(setargs_body);
        //setargs.setContract(new Contract(simple_base,
        //    create.expression(StandardOperator.Star , simple_base , check_body)));
        //setargs.setOrigin(m.getOrigin());
        //res.add_dynamic(setargs);
        
        Method unfold=new Method(Kind.Plain,method_name+"_unfold",args,tv);
        unfold.setBody(unfold_body);
        //TODO: fix contract
        unfold.setContract(new Contract(IfStatement.else_guard,body));
        unfold.setOrigin(m.getOrigin());
        res.add_dynamic(unfold);
        
        Method fold=new Method(Kind.Plain,method_name+"_fold",args,tv);
        fold.setBody(fold_body);
        //TODO: fix contract
        fold.setContract(new Contract(body,IfStatement.else_guard));
        fold.setOrigin(m.getOrigin());
        res.add_dynamic(fold);
        
        
        //TODO: add ref compare for recursive arguments to allow ref.next == next.ref checks!
      }
      {
        Method valid=new Method(Kind.Predicate,"valid",new String[0],valid_type);
        valid.setBody(valid_body);
        valid.setOrigin(c.getOrigin());
        res.add_dynamic(valid);        
      }
      result=res;
    }

    public void visit(ClassType t){
      String name[]=new String[t.name.length];
      int N=t.name.length-1;
      for(int i=0;i<N;i++)name[i]=t.name[i];
      name[N]=t.name[N]+"_ref";
      ClassType res=new ClassType(name);
      res.setOrigin(t.getOrigin());
      result=res;    
    }

    @Override
    public void visit(Method m) {
      String name=m.getName();
      int N=m.getArity();
      String args[]=new String[N];
      for(int i=0;i<N;i++){
        args[i]=m.getArgument(i);
      }
      //public ASTClass getParent(){ return cl; }
      FunctionType t=(FunctionType)m.getType().apply(this);
      Contract mc=m.getContract();
      Contract c=null;
      if (mc!=null){
        ASTNode pre=mc.pre_condition.apply(clause_rw);
        ASTNode post=mc.post_condition.apply(clause_rw);
        c=new Contract(pre,post,mc.modifiers);
      }
      Method.Kind kind=m.kind;
      if (kind==Method.Kind.Constructor){
        name+="_ref";
      }
      Method res=new Method(kind,name,args,t);
      res.setOrigin(m.getOrigin());
      if (c!=null) res.setContract(c);
      ASTNode body=m.getBody();
      if (body!=null) res.setBody(body.apply(this));
      result=res;
    }

    @Override
    public void visit(NameExpression e) {
      String name=e.getName();
      super.visit(e);
      if (name.equals("null")) return;
      switch(e.getKind()){
        case Argument:
          return;
        case Local:
          return;
        case Method:
          return;
        case Field:{
          NameExpression tmp=new NameExpression("ref");
          tmp.setKind(NameExpression.Kind.Field);
          tmp.setOrigin(e.getOrigin());
          result=new OperatorExpression(StandardOperator.Select,tmp,result);
          result.setOrigin(e.getOrigin());
          return;
        }
        default: throw new Error("name "+name+" has unhandled kind "+e.getKind()+" at "+e.getOrigin());
      }
    }

    public void visit(OperatorExpression e){
      StandardOperator op=e.getOperator();
      switch(op){
        case Unfold:
        case Fold:
        {
          ASTNode arg=e.getArg(0);
          if(arg instanceof MethodInvokation){
            String op_string=(op==StandardOperator.Fold)?"_fold":"_unfold";
            MethodInvokation apply=(MethodInvokation)arg;
            ASTNode object=apply.object.apply(copy_rw);
            NameExpression old_name=apply.method;
            ASTNode args[]=apply.map_args(copy_rw,new ASTNode[0]);
            
            NameExpression name=create.method_name(old_name.getName()+op_string);
            result=create.invokation(object ,apply.guarded,name,args);
            return;
          } else {
            throw new Error("don't know how to (un)fold "+arg.getClass());
          }
        }
        case Select:{
          ASTNode base=e.getArg(0).apply(copy_rw);
          NameExpression name=(NameExpression)e.getArg(1).apply(copy_rw);
          Type t=local_map.get(name.getName());
          if (t!=null && !(t instanceof ClassType)) {
              NameExpression tmp=new NameExpression("ref");
              tmp.setKind(NameExpression.Kind.Field);
              tmp.setOrigin(e.getOrigin());
              base=new OperatorExpression(StandardOperator.Select,base,tmp);
              base.setOrigin(e.getOrigin());
          }
          ASTNode res=new OperatorExpression(StandardOperator.Select,base,name);
          res.setOrigin(e.getOrigin());
          result=res;
          return;
        }
        default:
          super.visit(e);
          return;
      }
    }
  };

  /** The following variable contain the name of the predicate the rewriter is
   *  currently working on.
   */
  private String predicate;
  /**
   * This rewriter generates the Chalice valid predicate, when applied
   * to a predicate method body.
   */
  private AbstractRewriter valid_rw=new AbstractRewriter(){

    private ASTNode insert_ref(ASTNode expr){
      if (!(expr instanceof OperatorExpression)) Abort("cannot insert ref in %s",expr.getClass());
      OperatorExpression e=(OperatorExpression)expr;
      StandardOperator op=e.getOperator();
      if (op != StandardOperator.Select) Abort("cannot insert ref in %s expression",op);
      ASTNode name=e.getArg(1);
      ASTNode main=e.getArg(0);
      ASTNode ref=create.field_name("ref"); // TODO: check origin!
      main=create.expression(StandardOperator.Select,main,ref);
      return create.expression(StandardOperator.Select,main,name);
    }
    
    private ASTNode append_ref(ASTNode main){
      ASTNode ref=create.field_name("ref"); // TODO: check origin!
      return create.expression(StandardOperator.Select,main,ref);
    }
      private ASTNode refnullcheck(ASTNode object) {
          ASTNode ref_object=insert_ref(object);
          ASTNode nullname=new NameExpression("null");
          nullname.setOrigin(object);
          ASTNode null_object=new OperatorExpression(StandardOperator.NEQ,object,nullname);
          null_object.setOrigin(object);
          ASTNode null_ref_object=new OperatorExpression(StandardOperator.NEQ,ref_object,nullname);
          null_ref_object.setOrigin(object);
          ASTNode nulliff=new OperatorExpression(StandardOperator.IFF,null_object,null_ref_object);
          nulliff.setOrigin(object);
          return nulliff;
      }
      
      @Override
      public void visit(MethodInvokation e) {
        if (!e.guarded) throw new Error("cannot support unguarded calls yet.");
        
        ASTNode object=e.object;
        NameExpression pred=e.method;
        String name=pred.getName();
        
        NameExpression tmp;
        //tmp=new NameExpression(name+"_valid");
        //tmp.setOrigin(pred.getOrigin());
        //MethodInvokation valid=new MethodInvokation(object,true,tmp,new ASTNode[0]);
        //valid.setOrigin(e.getOrigin());

        int N=e.getArity();
        ASTNode args[]=new ASTNode[N];
        for(int i=0;i<N;i++){
          if (e.getArg(i) instanceof NameExpression){
            NameExpression par=(NameExpression)e.getArg(i);
            args[i]=new NameExpression(predicate+"_"+par.getName());
            args[i].setOrigin(par.getOrigin());
          } else {
            throw new Error("Bad first arg of Perm: "+e.getArg(0).getClass());
          }
        }
        tmp=new NameExpression(name+"_check");
        tmp.setOrigin(pred.getOrigin());
        MethodInvokation check=new MethodInvokation(object,true,tmp,args);
        check.setOrigin(e.getOrigin());
        
        //OperatorExpression res=new OperatorExpression(StandardOperator.Star,valid,check);
        //res.setOrigin(e.getOrigin());
        ASTNode res=check;
        
        res=new OperatorExpression(StandardOperator.Star,res,refnullcheck(object));
        res.setOrigin(e.getOrigin());
        result=res;
      }
      public void visit(OperatorExpression e){
        StandardOperator op=e.getOperator();
        int N=op.arity();
        ASTNode args[]=new ASTNode[N];
        switch(op){
          case Select:
            result=e.apply(copy_rw);
            if (!(e.getType() instanceof ClassType)){
              result=insert_ref(result);
            }
            return;
          case Star:
           System.err.print("*(");
           for(int i=0;i<N;i++){
              args[i]=e.getArg(i).apply(this);
            }
            result=new OperatorExpression(op,args);
            System.err.print(")");
            break;
          case Perm:
            {
              ASTNode name=e.getArg(0);
              args[0]=insert_ref(name);
            }
            if (e.getArg(1) instanceof NameExpression){
              NameExpression name=(NameExpression)e.getArg(1);
              args[1]=new NameExpression(predicate+"_"+name.getName());
              args[1].setOrigin(name.getOrigin());
            } else if (e.getArg(1) instanceof ConstantExpression){
              args[1]=e.getArg(1);
            } else {
              throw new Error("Bad second arg of Perm: "+e.getArg(1).getClass());
            }
            System.err.print("P");
            result=new OperatorExpression(op,args);
            break;
          case EQ:
            for(int i=0;i<N;i++){
              args[i]=e.getArg(i).apply(this);
            }
            result=new OperatorExpression(op,args);
            break;
          default:
            throw new Error("operator "+op+" unsupported in clause");
        }
        result.setOrigin(e.getOrigin());
      }
  };

  private HashMap<String, Type> local_map;

  /** create a reference encoding generator. */
  public ReferenceEncoding(){
    // The main rewriter works on ASTClass nodes only:
    //allow(ASTClass.class);
  }
  public void visit(ASTClass c) {
    String name=c.getName();
    if (name==null) {
      System.err.println("rewriting root class");
      if (c.getDynamicCount()>0) throw new Error("root class with dynamic content");
      ASTClass res=new ASTClass();
      res.setOrigin(c.getOrigin());
      int N=c.getStaticCount();
      for(int i=0;i<N;i++){
        ASTNode node=c.getStatic(i);
        if (node instanceof ASTClass){
          local_map=new HashMap<String,Type>();
          System.err.println("class is "+node.getClass());
          res.add_static(node.apply(data_rw));
          System.err.println("class is OK");
          res.add_static(node.apply(reference_rw));
        } else {
          res.add_static(node.apply(this));
        }
      }
      result=res;
      return;
    } else {
      System.err.println("rewriting class "+name);
      ASTClass res=new ASTClass(name,c.kind);
      res.setOrigin(c.getOrigin());
      int N=c.getStaticCount();
      for(int i=0;i<N;i++){
        res.add_static(c.getStatic(i).apply(this));
      }
      int M=c.getDynamicCount();
      for(int i=0;i<M;i++){
        res.add_dynamic(c.getDynamic(i).apply(this));
      }
      result=res;
      return;
    }
  }


}

