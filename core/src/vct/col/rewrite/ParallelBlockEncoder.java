package vct.col.rewrite;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Stack;
import java.util.concurrent.atomic.AtomicInteger;

import vct.col.ast.*;
import vct.col.ast.ASTSpecial.Kind;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.util.ASTUtils;
import vct.util.Configuration;


public class ParallelBlockEncoder extends AbstractRewriter {

  public ParallelBlockEncoder(ProgramUnit source) {
    super(source);
  }

  private int count=0;
  private Stack<ASTNode> inv_blocks=new Stack();
  private Stack<ParallelBlock> blocks=new Stack();
  private DeclarationStatement iter_decls[];
  private ASTNode iters_guard;
  private DeclarationStatement iter_decls_prime[];
  private ASTNode iters_guard_prime_before;
  private ASTNode iters_guard_prime_after;
  private Substitution sigma_prime;
  
  @Override
  public void visit(ParallelInvariant inv){
    inv_blocks.push(inv);
    BlockStatement block=rewrite(inv.block);
    block.prepend(create.special(ASTSpecial.Kind.Exhale,rewrite(inv.inv)));
    block.append(create.special(ASTSpecial.Kind.Inhale,rewrite(inv.inv)));
    result=block;
    inv_blocks.pop();
  }
  
  @Override
  public void visit(ParallelBlock pb){
    Contract c=pb.contract;
    if (c==null){
      Fail("parallel block without a contract");
    }
    blocks.push(pb);
    count++;
    String main_name="parallel_block_main_"+count;
    String check_name="parallel_block_check_"+count;
    String local_suffix="_local_"+count;
    BlockStatement res=create.block();
    BlockStatement call_with=create.block();
    Hashtable<String,Type> main_vars=free_vars(pb);
    Debug("free main vars: %s",main_vars);
    Hashtable<String,Type> check_vars=new Hashtable(main_vars);
    ContractBuilder main_cb=new ContractBuilder();
    ContractBuilder check_cb=new ContractBuilder();
    Hashtable<NameExpression,ASTNode> map=new Hashtable();
    Substitution sigma=new Substitution(source(),map);
    iter_decls = new DeclarationStatement[pb.iters.length];
    iter_decls_prime = new DeclarationStatement[pb.iters.length];
    ArrayList<ASTNode> guard_list=new ArrayList();
    ArrayList<ASTNode> guard_prime_list_before=new ArrayList();
    ArrayList<ASTNode> guard_prime_list_after=new ArrayList();
    Hashtable<NameExpression,ASTNode> prime=new Hashtable();
    for(int i=0;i<iter_decls.length;i++){
      iter_decls[i]=create.field_decl(pb.iters[i].name, pb.iters[i].getType());
      iter_decls_prime[i]=create.field_decl(pb.iters[i].name+"__prime", pb.iters[i].getType());
      ASTNode tmp=create.expression(StandardOperator.Member,create.unresolved_name(pb.iters[i].name),pb.iters[i].getInit());
      guard_list.add(tmp);
      check_cb.requires(tmp);
      check_cb.ensures(tmp);
      OperatorExpression range=(OperatorExpression)pb.iters[i].getInit();
      tmp=create.expression(StandardOperator.RangeSeq,range.getArg(0),create.unresolved_name(pb.iters[i].name));
      tmp=create.expression(StandardOperator.Member,create.unresolved_name(pb.iters[i].name+"__prime"),tmp);
      guard_prime_list_before.add(tmp);
      tmp=create.expression(StandardOperator.Plus,create.unresolved_name(pb.iters[i].name),create.constant(1));
      tmp=create.expression(StandardOperator.RangeSeq,tmp,range.getArg(1));
      tmp=create.expression(StandardOperator.Member,create.unresolved_name(pb.iters[i].name+"__prime"),tmp);
      guard_prime_list_after.add(tmp);
      check_vars.put(pb.iters[i].name,pb.iters[i].getType());
      prime.put(create.local_name(pb.iters[i].name),create.local_name(pb.iters[i].name+"__prime"));
    }
    iters_guard=create.fold(StandardOperator.And,guard_list);
    sigma_prime=new Substitution(source(),prime);
    iters_guard_prime_before=create.fold(StandardOperator.And,guard_prime_list_before);
    iters_guard_prime_after=create.fold(StandardOperator.And,guard_prime_list_after);
    
    for(ASTNode clause:ASTUtils.conjuncts(c.pre_condition, StandardOperator.Star)){
      check_cb.requires(clause);
      if (clause.getType().isBoolean()){
        main_cb.requires(create.forall(copy_rw.rewrite(iters_guard), rewrite(clause) , iter_decls));
      } else {
        main_cb.requires(create.starall(copy_rw.rewrite(iters_guard), rewrite(clause) , iter_decls));
      }
    }
    
    for(ASTNode clause:ASTUtils.conjuncts(c.post_condition, StandardOperator.Star)){
      check_cb.ensures(clause);
      if (clause.getType().isBoolean()){
        main_cb.ensures(create.forall(copy_rw.rewrite(iters_guard), rewrite(clause) , iter_decls));
      } else {
        main_cb.ensures(create.starall(copy_rw.rewrite(iters_guard), rewrite(clause) , iter_decls));
      }
    }
    currentTargetClass.add(create.method_decl(
        create.primitive_type(Sort.Void),
        check_cb.getContract(),
        check_name,
        gen_pars(check_vars),
        rewrite(pb.block)
    ));
    currentTargetClass.add(create.method_decl(
        create.primitive_type(Sort.Void),
        main_cb.getContract(),
        main_name,
        gen_pars(main_vars),
        null
    ));
    if (pb.get_before()!=null) for(ASTNode S:pb.get_before()){
      res.add(sigma.rewrite(S));
    }
    MethodInvokation call=gen_call(main_name,main_vars);
    call.set_before(call_with);
    res.add(call);
    if (pb.get_after()!=null) for(ASTNode S:pb.get_after()){
      res.add(rewrite(S));
    }
    blocks.pop();
    result=res;
  }
  
  @Override
  public void visit(ParallelBarrier pb){
    if (blocks.empty()){
      Fail("barrier outside of parallel block");
    }
    BlockStatement res=rewrite(pb.body);
    if (res==null){
      ContractBuilder main_cb=new ContractBuilder();
      ContractBuilder check_cb=new ContractBuilder();
      Hashtable<String,Type> main_vars=free_vars(pb);
      Hashtable<String,Type> check_vars=new Hashtable(main_vars);
      ParallelBlock blk=blocks.peek();
      ArrayList<ASTNode> guard_list=new ArrayList();
      ArrayList<DeclarationStatement> guard_decls=new ArrayList();
      for(DeclarationStatement decl:blk.iters){
        ASTNode tmp=create.expression(StandardOperator.Member,create.unresolved_name(decl.name),decl.getInit());
        guard_list.add(tmp);
        guard_decls.add(create.field_decl(decl.name, decl.getType()));
        check_vars.remove(decl.name);
      }
      ASTNode iters_guard=create.fold(StandardOperator.And,guard_list);
      DeclarationStatement iters_decl[]=guard_decls.toArray(new DeclarationStatement[0]);
      for(ASTNode clause:ASTUtils.conjuncts(pb.contract.pre_condition, StandardOperator.Star)){
        if (clause.getType().isBoolean()){
          check_cb.requires(create.forall(iters_guard, clause,iters_decl));
        } else {
          check_cb.requires(create.starall(iters_guard, clause,iters_decl));
        }
      }
      for(ASTNode clause:ASTUtils.conjuncts(pb.contract.post_condition, StandardOperator.Star)){
        if (clause.getType().isBoolean()){
          check_cb.ensures(create.forall(iters_guard, clause,iters_decl));
        } else {
          check_cb.ensures(create.starall(iters_guard, clause,iters_decl));
        }
      }
      count++;
      String main_name="barrier_main_"+count;
      String check_name="barrier_check_"+count;
      rewrite(pb.contract,main_cb);
      currentTargetClass.add(create.method_decl(
          create.primitive_type(Sort.Void),
          check_cb.getContract(),
          check_name,
          gen_pars(check_vars),
          create.block()
      ));
      currentTargetClass.add(create.method_decl(
          create.primitive_type(Sort.Void),
          main_cb.getContract(),
          main_name,
          gen_pars(main_vars),
          null
      ));
      result=gen_call(main_name,main_vars);
    } else {
      Abort("Cannot encode barrier with statements");
      //res.prepend(create.special(ASTSpecial.Kind.Inhale,blocks.peek().inv));
      for(ASTNode clause:ASTUtils.reverse(ASTUtils.conjuncts(pb.contract.pre_condition, StandardOperator.Star))){
        ASTNode cl;
        if (clause.getType().isBoolean()){
          cl=create.forall(copy_rw.rewrite(iters_guard_prime_before), sigma_prime.rewrite(clause) , iter_decls_prime);
        } else {
          cl=create.starall(copy_rw.rewrite(iters_guard_prime_before), sigma_prime.rewrite(clause) , iter_decls_prime);
        }
        res.prepend(create.special(ASTSpecial.Kind.Inhale,cl));
        if (clause.getType().isBoolean()){
          cl=create.forall(copy_rw.rewrite(iters_guard_prime_after), sigma_prime.rewrite(clause) , iter_decls_prime);
        } else {
          cl=create.starall(copy_rw.rewrite(iters_guard_prime_after), sigma_prime.rewrite(clause) , iter_decls_prime);
        }
        res.prepend(create.special(ASTSpecial.Kind.Inhale,cl));
      }
      
      //res.append(create.special(ASTSpecial.Kind.Exhale,blocks.peek().inv));
      for(ASTNode clause:ASTUtils.reverse(ASTUtils.conjuncts(pb.contract.post_condition, StandardOperator.Star))){
        ASTNode cl;
        if (clause.getType().isBoolean()){
          cl=create.forall(copy_rw.rewrite(iters_guard_prime_before), sigma_prime.rewrite(clause) , iter_decls_prime);
        } else {
          cl=create.starall(copy_rw.rewrite(iters_guard_prime_before), sigma_prime.rewrite(clause) , iter_decls_prime);
        }
        res.append(create.special(ASTSpecial.Kind.Exhale,cl));
        if (clause.getType().isBoolean()){
          cl=create.forall(copy_rw.rewrite(iters_guard_prime_after), sigma_prime.rewrite(clause) , iter_decls_prime);
        } else {
          cl=create.starall(copy_rw.rewrite(iters_guard_prime_after), sigma_prime.rewrite(clause) , iter_decls_prime);
        }
        res.append(create.special(ASTSpecial.Kind.Exhale,cl));
      }
      result=res;
    }
  }

  @Override
  public void visit(ParallelAtomic pb){
    if (inv_blocks.empty()){
      Fail("atomic region outside of parallel block");
    }
    BlockStatement res=rewrite(pb.block);
    HashSet<String> sync_list=new HashSet();
    for(ASTNode n:pb.sync_list) sync_list.add(n.toString());
    System.err.printf("sync list %s%n", sync_list);
    for(ASTNode ib:inv_blocks){
      if (ib instanceof ParallelInvariant){
        ParallelInvariant inv=(ParallelInvariant)ib;
        if (sync_list.contains(inv.label)){
          res.prepend(create.special(ASTSpecial.Kind.Inhale,inv.inv));
          res.append(create.special(ASTSpecial.Kind.Exhale,inv.inv));
        }
      } else {
        Abort("unexpected kind of invariant: %s",ib.getClass());
      }
    }
    result=res;
  }
}
