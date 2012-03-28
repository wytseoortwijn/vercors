package vct.col.rewrite;

import hre.ast.MessageOrigin;
import hre.ast.Origin;

import java.util.List;


import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.ConstantExpression;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.FunctionType;
import vct.col.ast.Method;
import vct.col.ast.Method.Kind;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import static hre.System.Fail;

/**
 * This rewriter adds the Java default specifications explicitly.
 *  
 * @author sccblom
 *
 */
public class JavaDefaultsRewriter extends AbstractRewriter {

  public ASTNode init_zero(){
    ASTNode _this=create.reserved_name("this");
    NameExpression init_name=create.method_name("init_zero");
    return create.invokation(_this,false,init_name);
  }

  public void visit(Method m){
    switch(m.kind){
    case Constructor:
    {
      // FIXME: this is almost a copy of the abstract rewriter method.
      String name=m.getName();
      int N=m.getArity();
      String args[]=new String[N];
      for(int i=0;i<N;i++){
        args[i]=m.getArgument(i);
      }
      FunctionType t=m.getType();
      Contract mc=m.getContract();
      Contract c=null;
      if (mc!=null){
        ASTNode pre=create.expression(StandardOperator.Star,mc.pre_condition.apply(this),init_zero());
        ASTNode post=mc.post_condition.apply(this);
        c=new Contract(pre,post,mc.modifiers);
      }
      Method.Kind kind=m.kind;
      Method res=new Method(Method.Kind.Plain,name+"_init",args,t);
      res.setOrigin(m.getOrigin());
      if (c!=null) res.setContract(c);
      ASTNode oldbody=m.getBody();
      if (oldbody!=null) {
        BlockStatement body=new BlockStatement();
        body.setOrigin(m);
        body.add_statement(create.expression(StandardOperator.Unfold,init_zero()));
        body.add_statement(oldbody.apply(this));
        res.setBody(body);
      }
      result=res;
      return;
    }
    default:
      super.visit(m);
      return;
    }
  }

  public void visit(ASTClass cl){
    int cons=0;
    {
      int N=cl.getDynamicCount();
      for(int i=0;i<N;i++){
        ASTNode member=cl.getDynamic(i);
        if (member instanceof Method){
          Method m=(Method)member;
          if (m.getKind()==Method.Kind.Constructor){
            cons++;
          }
        }
      }
    }
    super.visit(cl);
    ASTClass res=(ASTClass)result;
    if (!cl.isPackage()){
      String name=res.getName();
      int N=res.getDynamicCount();
      ASTNode tmp;
      Origin o=new MessageOrigin("init_zero for class "+name);
      ASTNode perm=new ConstantExpression(true);
      perm.setOrigin(o);
      ASTNode zero=new ConstantExpression(true);
      zero.setOrigin(o);
      ASTNode full=new ConstantExpression(100);
      full.setOrigin(o);
      for(int i=0;i<N;i++){
        ASTNode member=res.getDynamic(i);
        if (member instanceof DeclarationStatement){
          DeclarationStatement d=(DeclarationStatement)member;
          ASTNode var=new NameExpression(d.getName());
          var.setOrigin(o);
          tmp=new OperatorExpression(StandardOperator.Perm,var,full);
          tmp.setOrigin(o);
          perm=new OperatorExpression(StandardOperator.Star,perm,tmp);
          perm.setOrigin(o);
          if (d.getType() instanceof ClassType){
            tmp=create.reserved_name(o,"null");
            tmp=new OperatorExpression(StandardOperator.EQ,var,tmp);
            tmp.setOrigin(o);
            zero=new OperatorExpression(StandardOperator.Star,zero,tmp);
            zero.setOrigin(o);
          } else if (d.getType() instanceof PrimitiveType){
            PrimitiveType.Sort sort=((PrimitiveType)d.getType()).sort;
            switch(sort){
            case Integer:
              tmp=create.constant(o,0);
              break;
            case Long:
              tmp=create.constant(o,(long)0);
              break;
            case Double:
              /* TODO: fix the problem that the correct value is
              tmp=create.constant(o,(double)0);
              but chalice doesn't know about doubles, so we use */
              tmp=var;
              break;
            default:
              Fail("sort %s not supported yet",sort);
            }
            tmp=create.expression(o,StandardOperator.EQ,var,tmp);
            zero=new OperatorExpression(StandardOperator.Star,zero,tmp);
            zero.setOrigin(o);
          } else {
            Fail("java default value for %s unknown",d.getType().getClass());
          }
        }
      }
      Type bool=new PrimitiveType(Sort.Boolean);
      bool.setOrigin(o);
      tmp=new OperatorExpression(StandardOperator.Star,perm,zero);
      tmp.setOrigin(o);
      ASTNode init=new Method(Kind.Predicate, "init_zero", bool, null, new ASTNode[0], tmp);
      init.setOrigin(o);
      res.add_dynamic(init);
      init=new Method(Kind.Predicate, "init_random", bool, null, new ASTNode[0], perm);
      init.setOrigin(o);
      res.add_dynamic(init);
      if (cons==0) {
        /* TODO: properly add the implicit constructor, taking initializers
         * and invariants into account as well.
         */
        Type void_type=new PrimitiveType(Sort.Void);
        void_type.setOrigin(o);
        ASTNode body=new BlockStatement();
        body.setOrigin(o);
        Method constructor=new Method(Kind.Plain, name+"_init" , void_type, null, new ASTNode[0], body);
        constructor.setOrigin(o);
        ContractBuilder cb=new ContractBuilder();
        cb.requires(init_zero());
        constructor.setContract(cb.getContract());
        res.add_dynamic(constructor);
      }
    }
  }
}
