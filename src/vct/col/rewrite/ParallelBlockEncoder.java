package vct.col.rewrite;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.concurrent.atomic.AtomicInteger;

import vct.col.ast.*;
import vct.col.ast.ASTSpecial.Kind;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.util.ASTUtils;

public class ParallelBlockEncoder extends AbstractRewriter {

  public ParallelBlockEncoder(ProgramUnit source) {
    super(source);
  }

  private int count=0;
  private ParallelBlock currentPB=null;
  private DeclarationStatement iter_decls[];
  private ASTNode iters_guard;
  private DeclarationStatement iter_decls_prime[];
  private ASTNode iters_guard_prime;
  private Substitution sigma_prime;
  
  @Override
  public void visit(ParallelBlock pb){
    if (currentPB!=null){
      Fail("nested parallel blocks");
    }
    Contract c=pb.contract;
    if (c==null){
      Fail("parallel block without a contract");
    }
    currentPB=pb;
    count++;
    String main_name="parallel_block_main_"+count;
    String check_name="parallel_block_check_"+count;
    String local_suffix="_local_"+count;
    BlockStatement res=create.block();
    BlockStatement call_with=create.block();
    Hashtable<String,Type> main_vars=free_vars(pb);
    Warning("free main vars: %s",main_vars);
    Hashtable<String,Type> check_vars=new Hashtable(main_vars);
    ContractBuilder main_cb=new ContractBuilder();
    ContractBuilder check_cb=new ContractBuilder();
    Hashtable<NameExpression,ASTNode> map=new Hashtable();
    Substitution sigma=new Substitution(source(),map);
    iter_decls = new DeclarationStatement[pb.iters.length];
    iter_decls_prime = new DeclarationStatement[pb.iters.length];
    ArrayList<ASTNode> guard_list=new ArrayList();
    ArrayList<ASTNode> guard_prime_list=new ArrayList();
    Hashtable<NameExpression,ASTNode> prime=new Hashtable();
    for(int i=0;i<iter_decls.length;i++){
      iter_decls[i]=create.field_decl(pb.iters[i].name, pb.iters[i].getType());
      iter_decls_prime[i]=create.field_decl(pb.iters[i].name+"__prime", pb.iters[i].getType());
      ASTNode tmp=create.expression(StandardOperator.Member,create.unresolved_name(pb.iters[i].name),pb.iters[i].getInit());
      guard_list.add(tmp);
      check_cb.requires(tmp);
      check_cb.ensures(tmp);
      tmp=create.expression(StandardOperator.Member,create.unresolved_name(pb.iters[i].name+"__prime"),pb.iters[i].getInit());
      guard_prime_list.add(tmp);
      tmp=create.expression(StandardOperator.NEQ,create.unresolved_name(pb.iters[i].name+"__prime"),create.unresolved_name(pb.iters[i].name));
      guard_prime_list.add(tmp);      
      check_vars.put(pb.iters[i].name,pb.iters[i].getType());
      prime.put(create.local_name(pb.iters[i].name),create.local_name(pb.iters[i].name+"__prime"));
    }
    for(int i=0;i<pb.decls.length;i++){
      String name=pb.decls[i].name;
      Type t=pb.decls[i].getType();
      ASTNode init=pb.decls[i].getInit();
      if (t.isPrimitive(Sort.Array)){
        // Arrays become given parameters.
        String fname=name;
        res.add(create.field_decl(fname,t));
        String iname="i"+local_suffix;
        DeclarationStatement d=create.field_decl(iname,create.primitive_type(Sort.Integer));
        ASTNode guard=and(lte(constant(0),create.local_name(iname)),less(create.local_name(iname),t.getArg(1)));
        ASTNode field=create.expression(StandardOperator.Subscript,create.local_name(fname),create.local_name(iname));
        res.add(create.special(Kind.Inhale,create.starall(guard,
            create.expression(StandardOperator.Perm,field,create.reserved_name(ASTReserved.FullPerm)),d)));
        res.add(create.special(Kind.Inhale,create.forall(guard,
            create.expression(StandardOperator.EQ,field,init),d)));
        call_with.add(create.assignment(create.unresolved_name(name),create.local_name(fname)));
        check_cb.given(create.field_decl(name,t));
        main_cb.given(create.field_decl(name,t));
      } else {
        // Scalars become yielded parameters.
        check_cb.yields(rewrite(pb.decls[i]));
        main_cb.yields(create.field_decl(pb.decls[i].name, pb.decls[i].getType()));
        init=rewrite(init);
        if(init!=null){
          map.put(create.local_name(pb.decls[i].name), init);
        }
      }
    }
    iters_guard=create.fold(StandardOperator.And,guard_list);
    sigma_prime=new Substitution(source(),prime);
    iters_guard_prime=create.fold(StandardOperator.And,guard_prime_list);
    
    main_cb.requires(sigma.rewrite(pb.inv));
    for(ASTNode clause:ASTUtils.conjuncts(c.pre_condition, StandardOperator.Star)){
      check_cb.requires(clause);
      if (clause.getType().isBoolean()){
        main_cb.requires(create.forall(copy_rw.rewrite(iters_guard), rewrite(clause) , iter_decls));
      } else {
        main_cb.requires(create.starall(copy_rw.rewrite(iters_guard), rewrite(clause) , iter_decls));
      }
    }
    main_cb.ensures(pb.inv);
    for(ASTNode clause:ASTUtils.conjuncts(c.post_condition, StandardOperator.Star)){
      check_cb.ensures(clause);
      if (clause.getType().isBoolean()){
        main_cb.ensures(create.forall(copy_rw.rewrite(iters_guard), rewrite(clause) , iter_decls));
      } else {
        main_cb.ensures(create.starall(copy_rw.rewrite(iters_guard), rewrite(clause) , iter_decls));
      }
    }
    currentClass.add(create.method_decl(
        create.primitive_type(Sort.Void),
        check_cb.getContract(),
        check_name,
        gen_pars(check_vars),
        rewrite(pb.block)
    ));
    currentClass.add(create.method_decl(
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
    currentPB=null;
    result=res;
  }
  
  @Override
  public void visit(ParallelBarrier pb){
    if (currentPB==null){
      Fail("barrier outside of parallel block");
    }
    BlockStatement res=rewrite(pb.body);
    for(ASTNode clause:ASTUtils.conjuncts(pb.contract.pre_condition, StandardOperator.Star)){
      if (clause.getType().isBoolean()){
        clause=create.forall(copy_rw.rewrite(iters_guard_prime), sigma_prime.rewrite(clause) , iter_decls_prime);
      } else {
        clause=create.starall(copy_rw.rewrite(iters_guard_prime), sigma_prime.rewrite(clause) , iter_decls_prime);
      }
      res.prepend(create.special(ASTSpecial.Kind.Inhale,clause));
    }
    for(ASTNode clause:ASTUtils.conjuncts(pb.contract.post_condition, StandardOperator.Star)){
      if (clause.getType().isBoolean()){
        clause=create.forall(copy_rw.rewrite(iters_guard_prime), sigma_prime.rewrite(clause) , iter_decls_prime);
      } else {
        clause=create.starall(copy_rw.rewrite(iters_guard_prime), sigma_prime.rewrite(clause) , iter_decls_prime);
      }
      res.append(create.special(ASTSpecial.Kind.Exhale,clause));
    }

    res.prepend(create.special(ASTSpecial.Kind.Inhale,currentPB.inv));
    res.append(create.special(ASTSpecial.Kind.Exhale,currentPB.inv));
    result=res;
  }
  @Override
  public void visit(ParallelAtomic pb){
    if (currentPB==null){
      Fail("atomic region outside of parallel block");
    }
    BlockStatement res=rewrite(pb.block);
    res.prepend(create.special(ASTSpecial.Kind.Inhale,currentPB.inv));
    res.append(create.special(ASTSpecial.Kind.Exhale,currentPB.inv));
    result=res;
  }
}
