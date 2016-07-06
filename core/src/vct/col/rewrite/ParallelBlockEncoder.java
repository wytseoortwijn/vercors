package vct.col.rewrite;

import java.util.ArrayList;
import java.util.HashMap;
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
    Contract res=main_cb.getContract();
    blocks.pop();
    result=res;
  }
  
  @Override
  public void visit(ParallelBarrier pb){
    if (blocks.empty()){
      Fail("barrier outside of parallel block");
    }
    BlockStatement res=rewrite(pb.body);
    //if (res==null){
      ContractBuilder main_cb=new ContractBuilder();
      ContractBuilder check_cb=new ContractBuilder();
      Hashtable<String,Type> main_vars=free_vars(pb);
      Hashtable<String,Type> check_vars=new Hashtable(main_vars);
      ParallelBlock blk=null;
      for(ParallelBlock b:blocks){
        if(b.label.equals(pb.label)){
          blk=b;
        }
      }
      if(blk==null){
        Fail("Block %s not found on block stack",pb.label);
      }
      ArrayList<ASTNode> guard_list=new ArrayList();
      ArrayList<DeclarationStatement> guard_decls=new ArrayList();
      for(DeclarationStatement decl:blk.iters){
        ASTNode tmp=create.expression(StandardOperator.Member,create.unresolved_name(decl.name),decl.getInit());
        guard_list.add(tmp);
        tmp=create.expression(StandardOperator.Size,decl.getInit());
        tmp=create.expression(StandardOperator.GT,tmp,create.constant(0));
        check_cb.requires(tmp);
        check_cb.ensures(tmp);
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
      for(ASTNode ib:inv_blocks){
        if (ib instanceof ParallelInvariant){
          ParallelInvariant inv=(ParallelInvariant)ib;
          if (pb.invs.contains(inv.label)){
            check_cb.requires(inv.inv);
            check_cb.ensures(inv.inv);
          }
        } else {
          Abort("unexpected kind of invariant: %s",ib.getClass());
        }
      }
      currentTargetClass.add(create.method_decl(
          create.primitive_type(Sort.Void),
          check_cb.getContract(),
          check_name,
          gen_pars(check_vars),
          res
      ));
      currentTargetClass.add(create.method_decl(
          create.primitive_type(Sort.Void),
          main_cb.getContract(),
          main_name,
          gen_pars(main_vars),
          null
      ));
      result=gen_call(main_name,main_vars);
    //} else {
      
    if (false){
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
  public void visit(ParallelRegion region){
    count++;
    String main_name="parrallel_region_main_"+count;
    ContractBuilder main_cb=new ContractBuilder();
    Hashtable<String,Type> main_vars=free_vars(region.blocks);
    BlockStatement body;
    if (region.contract==null){
      for(ParallelBlock pb:region.blocks){
        Contract c=(Contract)rewrite((ASTNode)pb);
        main_cb.requires(c.pre_condition);
        main_cb.ensures(c.post_condition);
      }
      body=null;
    } else {
      rewrite(region.contract,main_cb);
      body=create.block();
      for(ParallelBlock pb:region.blocks){
        String block_name="block_check_"+(++count);
        Hashtable<String,Type> block_vars=free_vars(pb);
        
        Contract c=(Contract)rewrite((ASTNode)pb);     
        currentTargetClass.add(create.method_decl(
            create.primitive_type(Sort.Void),
            c,
            block_name,
            gen_pars(block_vars),
            null
        ));
        body.add(gen_call(block_name,block_vars));
      }
      HashMap<String,ParallelBlock> blocks=new HashMap();
      HashMap<String,HashSet<String>> may_deps=new HashMap();
      HashMap<String,HashSet<String>> must_deps=new HashMap();
      for(ParallelBlock pb:region.blocks){
        /* before is a set of blocks that are guaranteed
         * not to run concurrently with the current block.
         */
        HashSet<String> may=new HashSet();
        may.add(pb.label);
        HashSet<String> must=new HashSet();
        must.add(pb.label);
        for(int i=0;i<pb.deps.length;i++){
          ASTNode d=pb.deps[i];
          if (d instanceof NameExpression){
            String dep=d.toString();
            HashSet<String> trans=may_deps.get(dep);
            if (trans==null) {
              Fail("dependency %s of %s is unknown",dep,pb.label);
            }
            may.addAll(trans);
            must.addAll(must_deps.get(dep));
            ParallelBlock pb2=blocks.get(dep);
            ASTNode args[]=new ASTNode[pb2.iters.length];
            for(int j=0;j<args.length;j++){
              args[j]=create.reserved_name(ASTReserved.Any);
            }
            pb.deps[i]=create.invokation(null,null,dep, args);
          } else if (d instanceof MethodInvokation){
            MethodInvokation e=(MethodInvokation)d;
            String dep=e.method;
            HashSet<String> trans=must_deps.get(dep);
            if (trans==null) {
              Fail("dependency %s of %s is unknown",dep,pb.label);
            }
            boolean add=true;
            for(ASTNode a:e.getArgs()){
              if (!a.isReserved(ASTReserved.Any)){
                add=false;
                break;
              }
            }
            if (add){
              must.addAll(trans);
            }
            may.addAll(may_deps.get(dep));
          } else {
            Fail("cannot deal with dependency %s",d);
          }
        }
        for(String d:must_deps.keySet()){
          if (!must.contains(d)){
            gen_consistent(region,blocks.get(d),pb,may.contains(d));
            if (may.contains(d)){
              ParallelBlock pb2=blocks.get(d);
              ArrayList<ASTNode> conds=new ArrayList();
              ArrayList<DeclarationStatement> decls=new ArrayList();
              for(DeclarationStatement decl:pb2.iters){
                decls.add(create.field_decl("x_"+decl.name, decl.getType()));
              }
              HashMap<NameExpression, ASTNode> map=new HashMap();
              Substitution sigma=new Substitution(source(),map);
              for(DeclarationStatement decl:pb.iters){
                decls.add(create.field_decl("y_"+decl.name, decl.getType()));
                map.put(create.unresolved_name(decl.name),create.unresolved_name("y_"+decl.name));  
              }
              for(ASTNode dep_tmp:pb.deps){
                MethodInvokation dep=(MethodInvokation)dep_tmp;
                String dname=dep.method;
                if (pb2.label.equals(dname)){
                  ArrayList<ASTNode> parts=new ArrayList();
                  for(int i=0;i<pb2.iters.length;i++){
                    if (!dep.getArg(i).isReserved(ASTReserved.Any)){
                      parts.add(create.expression(StandardOperator.EQ,
                        create.argument_name("x_"+pb2.iters[i].name),
                        sigma.rewrite(dep.getArg(i))
                      ));
                    }
                  }
                  conds.add(create.fold(StandardOperator.And,parts));
                } else {
                  ParallelBlock pb1=blocks.get(dname);
                  if (must_deps.get(dname).contains(pb2.label)){
                    conds.add(create.constant(true));
                    break;
                  }
                  ArrayList<DeclarationStatement> exists=new ArrayList();
                  ASTNode args[]=new ASTNode[pb2.iters.length+pb1.iters.length];
                  for(int i=0;i<pb2.iters.length;i++){
                    args[i]=create.argument_name("x_"+pb2.iters[i].name);
                  }
                  for(int i=0;i<pb1.iters.length;i++){
                    if (dep.getArg(i).isReserved(ASTReserved.Any)){
                      args[pb2.iters.length+i]=create.unresolved_name("z_"+i);
                    } else {
                      args[pb2.iters.length+i]=sigma.rewrite(dep.getArg(i));
                    }
                  }
                  ASTNode cond=create.invokation(null,null,"before_" + pb2.label + "_" + pb1.label, args);
                  if (exists.size()>0){
                    cond=create.exists(create.constant(true),cond,exists.toArray(new DeclarationStatement[0]));
                  }
                  conds.add(cond);
                }
              }
              ASTNode cond=create.fold(StandardOperator.Or, conds);
              currentTargetClass.add(create.function_decl(
                  create.primitive_type(Sort.Boolean),
                  null,
                  "before_"+pb2.label+"_"+pb.label,
                  decls.toArray(new DeclarationStatement[0]),
                  cond
              ));
            }
          }
        }
        may_deps.put(pb.label,may);
        must_deps.put(pb.label,must);
        blocks.put(pb.label,pb);
      }
    }
    currentTargetClass.add(create.method_decl(
        create.primitive_type(Sort.Void),
        main_cb.getContract(),
        main_name,
        gen_pars(main_vars),
        body
    ));
    result=gen_call(main_name,main_vars);
  }
  
  private void gen_consistent(ParallelRegion region, ParallelBlock pb1, ParallelBlock pb2, boolean guard) {
    ASTNode pre_condition=region.contract.pre_condition;
    HashMap<NameExpression, ASTNode> map1=new HashMap();
    Substitution sigma1=new Substitution(source(),map1);
    HashMap<NameExpression, ASTNode> map2=new HashMap();
    Substitution sigma2=new Substitution(source(),map2);
    ContractBuilder cb=new ContractBuilder();
    cb.requires(pre_condition);
    Hashtable<String,Type> main_vars=free_vars(pre_condition);
    ArrayList<ASTNode> list=new ArrayList();
    int N=0;
    for(DeclarationStatement decl:pb1.iters){
      String name="x"+(++N);
      main_vars.put(name,decl.getType());
      map1.put(create.unresolved_name(decl.name),create.unresolved_name(name));
      OperatorExpression range=(OperatorExpression)decl.getInit();
      cb.requires(create.expression(
          StandardOperator.LTE,rewrite(range.getArg(0)),create.unresolved_name(name))
      );
      cb.requires(create.expression(
          StandardOperator.LT,create.unresolved_name(name),rewrite(range.getArg(1)))
      );
    }
    for(DeclarationStatement decl:pb2.iters){
      String name="x"+(++N);
      main_vars.put(name,decl.getType());
      map2.put(create.unresolved_name(decl.name),create.unresolved_name(name));
      OperatorExpression range=(OperatorExpression)decl.getInit();
      cb.requires(create.expression(
          StandardOperator.LTE,rewrite(range.getArg(0)),create.unresolved_name(name))
      );
      cb.requires(create.expression(
          StandardOperator.LT,create.unresolved_name(name),rewrite(range.getArg(1)))
      );
    }
    ASTNode args[]=new ASTNode[N];
    for(int i=0;i<N;){
      args[i]=create.argument_name("x"+(++i));
    }
    for(ASTNode clause:ASTUtils.conjuncts(pb1.contract.pre_condition,StandardOperator.Star)){
      if(clause.getType().isResource()){
        list.add(sigma1.rewrite(clause));
      }
    }
    for(ASTNode clause:ASTUtils.conjuncts(pb2.contract.pre_condition,StandardOperator.Star)){
      if(clause.getType().isResource()){
        list.add(sigma2.rewrite(clause));
      }      
    }
    ASTNode body=create.expression(StandardOperator.Assert,create.fold(StandardOperator.Star, list));
    if (guard) {
      body=create.ifthenelse(create.expression(StandardOperator.Not,
              create.invokation(null, null, "before_"+pb1.label+"_"+pb2.label , args)),
            create.block(
              body
            )
          );
    }
    currentTargetClass.add(create.method_decl(
        create.primitive_type(Sort.Void),
        cb.getContract(),
        "check_"+pb1.label+"_"+pb2.label,
        gen_pars(main_vars),
        create.block(
          body
        )
    ));
    
  }

  @Override
  public void visit(ParallelAtomic pa){
    BlockStatement block=rewrite(pa.block);
    for(ASTNode node:pa.sync_list){
      if (node instanceof NameExpression){
        NameExpression name=(NameExpression)node;
        if (name.getKind()==NameExpression.Kind.Label){
          boolean found=false;
          for(ASTNode ib:inv_blocks){
            if (ib instanceof ParallelInvariant){
              ParallelInvariant inv=(ParallelInvariant)ib;
              if (inv.label.equals(name.toString())){
                block.prepend(create.special(ASTSpecial.Kind.Inhale,inv.inv));
                block.append(create.special(ASTSpecial.Kind.Exhale,inv.inv));
                found=true;
              }
            }
          }
          if (found){
            continue;
          }
          Fail("Could not find an invariant labeled %s",name);
        }
      }
      block.prepend(create.expression(StandardOperator.Unfold,create.invokation(rewrite(node),null,"csl_invariant")));
      block.prepend(create.special(ASTSpecial.Kind.Inhale,create.invokation(rewrite(node),null,"csl_invariant")));
      block.append(create.expression(StandardOperator.Fold,create.invokation(rewrite(node),null,"csl_invariant")));
      block.append(create.special(ASTSpecial.Kind.Exhale,create.invokation(rewrite(node),null,"csl_invariant")));
    }
    result=block;
  }


  public void vissit(ParallelAtomic pb){
    BlockStatement res=rewrite(pb.block);
    
    
    /*
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
    */
    result=res;
  }
}
