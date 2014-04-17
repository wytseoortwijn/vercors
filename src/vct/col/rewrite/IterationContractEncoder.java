package vct.col.rewrite;

import hre.ast.BranchOrigin;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.concurrent.atomic.AtomicInteger;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.BindingExpression.Binder;
import vct.col.ast.BlockStatement;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.ast.VariableDeclaration;
import vct.col.util.ASTUtils;
import vct.col.util.NameScanner;
import vct.col.util.OriginWrapper;

public class IterationContractEncoder extends AbstractRewriter {

  private AtomicInteger counter=new AtomicInteger();
    
  public IterationContractEncoder(ProgramUnit arg) {
    super(arg);
  }

  public void visit(LoopStatement s){
    Contract c=s.getContract();
    if (c!=null && (c.pre_condition != c.default_true || c.post_condition != c.default_true)){
      Warning("processing iteration contract");
      Hashtable<String,Type> vars=new Hashtable<String,Type>();
      s.getBody().accept(new NameScanner(vars));
      c.accept(new NameScanner(vars));
      s.getEntryGuard().accept(new NameScanner(vars));
      Hashtable<String,Type> iters=new Hashtable<String,Type>();
      s.getUpdateBlock().accept(new NameScanner(iters));
      for(String var:iters.keySet()){
        System.err.printf("iter %s : %s%n", var,iters.get(var));
      }
      int N=counter.incrementAndGet();
      String main_name="loop_main_"+N;
      String body_name="loop_body_"+N;
      ArrayList<DeclarationStatement> main_decl=new ArrayList();
      ArrayList<ASTNode> main_args=new ArrayList();
      ArrayList<DeclarationStatement> body_decl=new ArrayList();
      ContractBuilder cb=new ContractBuilder();
      ASTNode low=s.getInitBlock();
      if (low instanceof BlockStatement){
        low=((BlockStatement)low).getStatement(0);
      }
      String var_name=((DeclarationStatement)low).getName();
      low=((DeclarationStatement)low).getInit();
      ASTNode high=s.getEntryGuard();
      StandardOperator op=((OperatorExpression)high).getOperator();
      high=((OperatorExpression)high).getArg(1);
      
      ASTNode guard=create.expression(StandardOperator.And,
          create.expression(StandardOperator.LTE,low,create.unresolved_name(var_name)),
          create.expression(op,create.unresolved_name(var_name),high)
      );
      for(ASTNode clause:ASTUtils.conjuncts(c.invariant)){
        if (clause.getType().isBoolean()){
          cb.appendInvariant(create.forall(
              copy_rw.rewrite(guard),
              copy_rw.rewrite(clause),
              create.field_decl(var_name,create.primitive_type(Sort.Integer))));
        } else {
          cb.appendInvariant(create.starall(
            copy_rw.rewrite(guard),
            copy_rw.rewrite(clause),
            create.field_decl(var_name,create.primitive_type(Sort.Integer))));
        }
      }
      for(ASTNode clause:ASTUtils.conjuncts(c.pre_condition)){
        if (clause.getType().isBoolean()){
          cb.requires(create.forall(
              copy_rw.rewrite(guard),
              copy_rw.rewrite(clause),
              create.field_decl(var_name,create.primitive_type(Sort.Integer))));
        } else {
          cb.requires(create.starall(
            copy_rw.rewrite(guard),
            copy_rw.rewrite(clause),
            create.field_decl(var_name,create.primitive_type(Sort.Integer))));
        }
      }
      for(ASTNode clause:ASTUtils.conjuncts(c.post_condition)){
        if (clause.getType().isBoolean()){
          cb.ensures(create.forall(
            copy_rw.rewrite(guard),
            copy_rw.rewrite(clause),
            create.field_decl(var_name,create.primitive_type(Sort.Integer))));
        } else {
          cb.ensures(create.starall(
              copy_rw.rewrite(guard),
              copy_rw.rewrite(clause),
              create.field_decl(var_name,create.primitive_type(Sort.Integer))));
        }
      }
      for(String var:vars.keySet()){
        System.err.printf("var %s : %s%n", var,vars.get(var));
        body_decl.add(create.field_decl(var,copy_rw.rewrite(vars.get(var))));
        if (iters.containsKey(var)) continue;
        main_decl.add(create.field_decl(var,copy_rw.rewrite(vars.get(var))));
        main_args.add(create.unresolved_name(var));
      }
      Method main_method=create.method_decl(
          create.primitive_type(PrimitiveType.Sort.Void),
          cb.getContract(), 
          main_name, 
          main_decl.toArray(new DeclarationStatement[0]),
          null);
      BranchOrigin branch=new BranchOrigin("Loop Contract",null);
      OriginWrapper.wrap(null,main_method, branch);
      currentClass.add_dynamic(main_method);
      Method main_body=create.method_decl(
          create.primitive_type(PrimitiveType.Sort.Void),
          rewrite(c),
          body_name,
          body_decl.toArray(new DeclarationStatement[0]),
          rewrite(s.getBody())
      );
      branch=new BranchOrigin("Iteration Body",null);
      OriginWrapper.wrap(null,main_body, branch);
      System.out.printf("generated %s at %s%n",main_body.name,main_body.getOrigin());
      currentClass.add_dynamic(main_body);
      result=create.invokation(null,null,main_name,main_args.toArray(new ASTNode[0]));
      branch=new BranchOrigin("Parallel Loop",null);
      OriginWrapper.wrap(null,result, branch);
    } else {
      super.visit(s);
    }
  }
  
}
