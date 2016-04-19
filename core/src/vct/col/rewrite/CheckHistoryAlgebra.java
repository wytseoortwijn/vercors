package vct.col.rewrite;

import hre.HREError;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.concurrent.atomic.AtomicInteger;

import vct.col.ast.BindingExpression.Binder;
import vct.col.ast.Method.Kind;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.*;
import vct.col.util.ASTUtils;
import vct.util.Configuration;
import static vct.col.ast.StandardOperator.Value;
import static vct.col.ast.StandardOperator.Perm;
import static vct.col.ast.StandardOperator.PointsTo;
import static vct.col.ast.StandardOperator.EQ;
import static vct.col.ast.StandardOperator.Old;
import static vct.col.ast.ASTReserved.FullPerm;

public class CheckHistoryAlgebra extends AbstractRewriter {
  
  private AtomicInteger count=new AtomicInteger();
  
  public static enum Mode { AxiomVerification, ProgramVerification };
  public final Mode mode;
  
  public CheckHistoryAlgebra(ProgramUnit source,Mode mode) {
    super(source);
    this.mode=mode;
  }

  private Hashtable<String,String> composite_map;
  private Hashtable<String,Method> process_map;
  
  private Type adt_type;
  private AxiomaticDataType adt;
  private ASTClass hist_class;
  
  @Override
  public void visit(ASTClass cl){
    boolean is_algebra=false;
    for(Method m:cl.dynamicMethods()){
      is_algebra|=m.getReturnType().isPrimitive(Sort.Process);
    }
    if (is_algebra){
      boolean is_history=cl.name.equals("History");
      composite_map=new Hashtable<String,String>();
      process_map=new Hashtable<String,Method>();
      adt=create.adt("Process");
      adt_type=create.class_type("Process");
      DeclarationStatement proc_p1=create.field_decl("p1", adt_type);
      DeclarationStatement proc_p2=create.field_decl("p2", adt_type);
      adt.add_cons(create.function_decl(adt_type,null,"p_empty",
          new DeclarationStatement[]{},null));
      adt.add_cons(create.function_decl(adt_type,null,"p_merge",
          new DeclarationStatement[]{proc_p1,proc_p2},null));
      adt.add_cons(create.function_decl(adt_type,null,"p_seq",
          new DeclarationStatement[]{proc_p1,proc_p2},null));
      adt.add_axiom(create.axiom("empty_1L",
          create.forall(create.constant(true),
              create.expression(StandardOperator.EQ,
                  create.invokation(null, null, "p_merge",
                      create.invokation(null, null, "p_empty"),
                      create.local_name("p")
                  ),
                  create.local_name("p")
              ),create.field_decl("p", adt_type)
          )
      ));
      adt.add_axiom(create.axiom("empty_2L",
          create.forall(create.constant(true),
              create.expression(StandardOperator.EQ,
                  create.invokation(null, null, "p_seq",
                      create.invokation(null, null, "p_empty"),
                      create.local_name("p")
                  ),
                  create.local_name("p")
              ),create.field_decl("p", adt_type)
          )
      ));
      adt.add_axiom(create.axiom("empty_2R",
          create.forall(create.constant(true),
              create.expression(StandardOperator.EQ,
                  create.invokation(null, null, "p_seq",
                      create.local_name("p"),
                      create.invokation(null, null, "p_empty")
                  ),
                  create.local_name("p")
              ),create.field_decl("p", adt_type)
          )
      ));
      adt.add_axiom(create.axiom("seq_assoc",
          create.binder(
              Binder.FORALL,
              create.primitive_type(Sort.Boolean),
              new DeclarationStatement[]{
                 create.field_decl("p1", adt_type)
                ,create.field_decl("p2", adt_type)
                ,create.field_decl("p3", adt_type)},
              new ASTNode[][]{
                new ASTNode[]{create.invokation(null, null, "p_seq",
                    create.invokation(null, null,"p_seq",create.local_name("p1"),create.local_name("p2")),
                    create.local_name("p3")
                )}
              },
              create.constant(true),
              create.expression(StandardOperator.EQ,
                  create.invokation(null, null, "p_seq",
                      create.invokation(null, null,"p_seq",create.local_name("p1"),create.local_name("p2")),
                      create.local_name("p3")
                  ),
                  create.invokation(null, null, "p_seq",create.local_name("p1"),
                      create.invokation(null, null, "p_seq",create.local_name("p2"),create.local_name("p3"))
                  )
              )
          )
      ));
      target().add(adt);
      switch(mode){
      case AxiomVerification:{
        ASTClass res=create.new_class(cl.name,new DeclarationStatement[0],null);
        for(Method m:cl.dynamicMethods()){
          if (m.getKind()==Method.Kind.Constructor){
            continue;
          } else if (m.getReturnType().isPrimitive(Sort.Process)){
            add_process_to_adt(m);
          } else if (m.getReturnType().isPrimitive(Sort.Resource)) {
            // drop predicate.
          } else {
            res.add_dynamic(rewrite(m));
          }
        }
        result=res;
        return;        
      }
      case ProgramVerification:{
        hist_class=create.new_class(cl.name,new DeclarationStatement[0],null);;
        for(Method m:cl.dynamicMethods()){
          if (m.getKind()==Method.Kind.Constructor){
            continue; //res.add_dynamic(rewrite(m));
          } else if (m.getReturnType().isPrimitive(Sort.Process)){
            add_process_to_adt(m);
            if (m.getBody()==null) {
              add_begin_and_commit_to_class(m,is_history);
            }
          } else if (m.getReturnType().isPrimitive(Sort.Resource)) {
            hist_class.add(rewrite(m));
          } else {
            add_lemma_to_adt(m);
          }
        }
        for(DeclarationStatement m:cl.dynamicFields()){
          hist_class.add_dynamic(create.field_decl(m.name+"_hist_value",m.getType(),rewrite(m.getInit())));
          hist_class.add_dynamic(create.field_decl(m.name+"_hist_mode",create.primitive_type(Sort.Integer)));
          hist_class.add_dynamic(create.field_decl(m.name+"_hist_init",m.getType()));
          hist_class.add_dynamic(create.field_decl(m.name+"_hist_act",m.getType()));
          add_setters_and_getter(hist_class,m.name,m.getType());
        }
        
        add_begin_hist_method(cl);
        add_split_merge_methods(cl);

        DeclarationStatement args[]=new DeclarationStatement[2];
        args[0]=create.field_decl("frac",create.primitive_type(Sort.Fraction));
        args[1]=create.field_decl("proc",adt_type);
        hist_class.add(create.predicate("hist_idle", null, args));
        create.addZeroConstructor(hist_class);
        result=hist_class;
        return;
      }}
    } else {
      super.visit(cl);
    }
    /* skip generating program checking class 
    HashSet<NameExpression> hist_set=new HashSet<NameExpression>();
    for(Method m:cl.dynamicMethods()){
      if (!m.getReturnType().isPrimitive(Sort.Process)) continue;
      ASTNode body=m.getBody();
      process_map.put(m.name, m);
      for(ASTNode n:m.getContract().modifies){
        if (n instanceof NameExpression){
          hist_set.add((NameExpression)n);
        } else if (n instanceof Dereference) {
          Dereference d=(Dereference)n;
          hist_set.add(create.field_name(d.field));
        } else {
          Fail("unexpected entry in modifies clause");
        }
      }
      if (body==null) continue;
      if(body.isa(StandardOperator.Or)){
        String composite=":";
        for(ASTNode p:ASTUtils.conjuncts(body, StandardOperator.Or)){
          if (p instanceof MethodInvokation){
            composite+=((MethodInvokation)p).method+":";
          } else {
            Fail("misformed parallel composition");
          }
        }
        // TODO: check if arguments are passed in-order.
        // That is p(a,b)=q(a)||q(b) is allowed
        // p(a,b)=q(b)||q(a) is forbidden.
        composite_map.put(composite,m.name);
        Warning("mapping %s to %s",composite,m.name);
      }
    }
    super.visit(cl);
    ASTClass res=(ASTClass)result;
    for(NameExpression n:hist_set){
      String name=n.getName();
      VariableInfo info=variables.lookup(name);
      Type t=((DeclarationStatement)info.reference).getType();
      res.add(create.field_decl(n.getName()+"_old",copy_rw.rewrite(t)));
    }
    Type ref_t=create.class_type("Ref");
    
    res.add(create.predicate("hist_idle", create.constant(true),
        new DeclarationStatement[]{
          create.field_decl("ref",ref_t),
          create.field_decl("p",adt_type)}));
    for(Method m:cl.dynamicMethods()){
      if (!m.getReturnType().isPrimitive(Sort.Process)) continue;
      if (m.getBody()!=null) continue;
      // m defines an action.
      create.enter();
      create.setOrigin(m.getOrigin());
      ContractBuilder begin_cb=new ContractBuilder();
      ArrayList<DeclarationStatement> begin_args=new ArrayList();
      ContractBuilder commit_cb=new ContractBuilder();
      ArrayList<DeclarationStatement> commit_args=new ArrayList();
      HashSet<NameExpression> mod_set=new HashSet<NameExpression>();
      Contract c=m.getContract();
      begin_args.add(create.field_decl("ref", ref_t));
      begin_args.add(create.field_decl("p", adt_type));
      begin_cb.requires(create.invokation(null,null,"hist_idle",create.local_name("ref"),create.local_name("p")));
      begin_cb.ensures(create.invokation(null,null,"hist_"+m.name,create.local_name("ref"),create.local_name("p")));
      commit_args.add(create.field_decl("ref", ref_t));
      commit_args.add(create.field_decl("p", adt_type));
      commit_cb.requires(create.invokation(null,null,"hist_"+m.name,create.local_name("ref"),create.local_name("p")));
      commit_cb.ensures(create.invokation(null,null,"hist_idle",
          create.local_name("ref"),
          create.invokation(null,null,"p_seq",create.local_name("p"),
              create.invokation(null,null,"p_"+m.name))));
      HashMap<NameExpression,ASTNode> old_map=new HashMap();
      HashMap<NameExpression,ASTNode> new_map=new HashMap();
      for(ASTNode n:c.modifies){
        NameExpression name;
        if (n instanceof NameExpression){
          name=((NameExpression)n);
        } else if (n instanceof Dereference) {
          Dereference d=(Dereference)n;
          name=(create.field_name(d.field));
        } else {
          Fail("unexpected entry in modifies clause");
          name=null;
        }
        ASTNode var=create.dereference(create.local_name("ref"),name.getName());
        NameExpression name_old=create.field_name(name.getName()+"_old");
        mod_set.add(name);
        old_map.put(name,name_old);
        new_map.put(name,var);
        ASTNode half=create.expression(StandardOperator.Div,create.constant(1),create.constant(2));
        ASTNode full=create.reserved_name(ASTReserved.FullPerm);
        begin_cb.requires(create.expression(Perm,var,full));
        begin_cb.ensures(create.expression(Perm,var,full));
        begin_cb.ensures(create.expression(StandardOperator.EQ,var,create.expression(StandardOperator.Old,var)));
        begin_cb.ensures(create.expression(Perm,name_old,half));
        begin_cb.ensures(create.expression(StandardOperator.EQ,var,name_old));
        commit_cb.requires(create.expression(Perm,var,full));
        commit_cb.ensures(create.expression(Perm,var,full));
        commit_cb.ensures(create.expression(StandardOperator.EQ,var,create.expression(StandardOperator.Old,var)));
        commit_cb.requires(create.expression(Perm,name_old,half));
      }
      // TODO rewrite based on the set of modified variables, rather than trusting simp!
      Simplify simp=new Simplify(this);
      Substitution sigma=new Substitution(source(),old_map);
      ApplyOld rw_old=new ApplyOld(sigma);
      Substitution rw_new=new Substitution(source(),new_map);
      commit_cb.requires(rw_new.rewrite(rw_old.rewrite(simp.rewrite(c.post_condition))));
      res.add(create.method_decl(
          create.primitive_type(Sort.Void),
          begin_cb.getContract(),
          m.name+"_begin",
          begin_args.toArray(new DeclarationStatement[0]),
          null
      ));
      res.add(create.method_decl(
          create.primitive_type(Sort.Void),
          commit_cb.getContract(),
          m.name+"_commit",
          commit_args.toArray(new DeclarationStatement[0]),
          null
      ));
      res.add(create.predicate("hist_"+m.name, create.constant(true),
          new DeclarationStatement[]{
            create.field_decl("ref",ref_t),
            create.field_decl("p",adt_type)}));
      create.leave();
    }
    result=res;
    */
  }

  private void add_setters_and_getter(ASTClass cl, String name, Type type) {
    ContractBuilder free_set_cb=new ContractBuilder();
    ContractBuilder hist_set_cb=new ContractBuilder();
    ContractBuilder free_get_cb=new ContractBuilder();
    ContractBuilder hist_get_cb=new ContractBuilder();
    ASTNode half=create.expression(StandardOperator.Div,create.constant(1),create.constant(2));
    ASTNode var=create.field_name(name+"_hist_value");
    ASTNode val=create.local_name("value");
    ASTNode mode=create.field_name(name+"_hist_mode");
    ASTNode full=create.reserved_name(FullPerm);
    ASTNode free=create.constant(0);
    ASTNode hist=create.constant(2);
    free_set_cb.requires(create.expression(Perm,var,full));
    free_set_cb.requires(create.expression(PointsTo,mode,half,free));
    free_set_cb.ensures(create.expression(PointsTo,var,full,val));
    free_set_cb.ensures(create.expression(PointsTo,mode,half,free));
    hist_set_cb.requires(create.expression(Perm,var,full));
    hist_set_cb.requires(create.expression(PointsTo,mode,half,hist));
    hist_set_cb.ensures(create.expression(PointsTo,var,full,val));
    hist_set_cb.ensures(create.expression(PointsTo,mode,half,hist));
    free_get_cb.requires(create.expression(Value,var));
    //free_get_cb.requires(create.expression(Value,mode));
    //free_get_cb.requires(create.expression(EQ,mode,free));
    hist_get_cb.requires(create.expression(Value,var));
    //hist_get_cb.requires(create.expression(Value,mode));
    //hist_get_cb.requires(create.expression(EQ,mode,hist));    
    cl.add_dynamic(create.method_decl(
        create.primitive_type(Sort.Void),
        free_set_cb.getContract(),
        "free_set_"+name,
        new DeclarationStatement[]{create.field_decl("value", type)},
        null
    ));
    cl.add_dynamic(create.method_decl(
        create.primitive_type(Sort.Void),
        hist_set_cb.getContract(),
        "hist_set_"+name,
        new DeclarationStatement[]{create.field_decl("value", type)},
        null
    ));
    cl.add_dynamic(create.function_decl(
        type,
        free_get_cb.getContract(),
        "free_get_"+name,
        new DeclarationStatement[0],
        var
    ));
    cl.add_dynamic(create.function_decl(
        type,
        hist_get_cb.getContract(),
        "hist_get_"+name,
        new DeclarationStatement[0],
        var
    ));
  }

  protected void add_begin_hist_method(ASTClass cl) {
    Method begin_hist;
    boolean hist=hist_class.getName().equals("History");
    ContractBuilder cb=new ContractBuilder();
    for(DeclarationStatement d:cl.dynamicFields()){
      cb.requires(create.expression(Perm,create.field_name(d.name+"_hist_value"),create.reserved_name(FullPerm)));
      cb.requires(create.expression(PointsTo,create.field_name(d.name+"_hist_mode"),
          create.reserved_name(FullPerm),create.constant(hist?0:1)));
      cb.requires(create.expression(Perm,create.field_name(d.name+"_hist_init"),create.reserved_name(FullPerm)));
      if (hist){
        cb.requires(create.expression(Perm,create.field_name(d.name+"_hist_act"),create.reserved_name(FullPerm)));
      } else {
        cb.ensures(create.expression(Perm,create.field_name(d.name+"_hist_act"),create.reserved_name(FullPerm)));
      }
      cb.ensures(create.expression(Perm,create.field_name(d.name+"_hist_value"),create.reserved_name(FullPerm)));
      cb.ensures(create.expression(PointsTo,create.field_name(d.name+"_hist_mode"),
          create.reserved_name(FullPerm),create.constant(hist?1:0)));
      cb.ensures(create.expression(Perm,create.field_name(d.name+"_hist_init"),create.reserved_name(FullPerm)));
      cb.ensures(create.expression(EQ
          , create.field_name(d.name+"_hist_value")
          , create.expression(Old,create.field_name(d.name+"_hist_value"))
      ));
      cb.ensures(create.expression(EQ
          , create.field_name(d.name+"_hist_init")
          , create.expression(Old,create.field_name(hist?d.name+"_hist_value":d.name+"_hist_init"))
      ));
      if (!hist){
        cb.ensures(create.expression(EQ
            , create.field_name(d.name+"_hist_init")
            , create.field_name(d.name+"_hist_value")
        ));
      }
    }
    ASTNode tmp=create.invokation(null, null, "hist_idle",
        create.reserved_name(ASTReserved.FullPerm),
        create.invokation(null, null, "p_empty")
    );
    if (hist){ cb.ensures(tmp); } else { cb.requires(tmp); }
    begin_hist=create.method_decl(
        create.primitive_type(Sort.Void),
        cb.getContract(),
        hist?"begin_hist":"end_future",
        new DeclarationStatement[0],
        null
    );
    hist_class.add(begin_hist);
    System.out.printf("%s%n",Configuration.getDiagSyntax().print(begin_hist));

  }

  protected void add_split_merge_methods(ASTClass cl) {
    DeclarationStatement args[]=new DeclarationStatement[4];
    args[0]=create.field_decl("frac1",create.primitive_type(Sort.Fraction));
    args[1]=create.field_decl("proc1",adt_type);
    args[2]=create.field_decl("frac2",create.primitive_type(Sort.Fraction));
    args[3]=create.field_decl("proc2",adt_type);
    
    ASTNode split1=create.invokation(null, null, "hist_idle",
        create.local_name("frac1"),create.local_name("proc1")
    );
    ASTNode split2=create.invokation(null, null, "hist_idle",
        create.local_name("frac2"),create.local_name("proc2")
    );
    ASTNode merge=create.invokation(null, null, "hist_idle",
        create.expression(StandardOperator.Plus,create.local_name("frac1"),create.local_name("frac2")),
        create.invokation(null, null,"p_merge",create.local_name("proc1"),create.local_name("proc2"))
    );
    ContractBuilder split_cb=new ContractBuilder();
    ContractBuilder merge_cb=new ContractBuilder();
    
    split_cb.requires(merge);
    split_cb.ensures(split1);
    split_cb.ensures(split2);
    
    merge_cb.requires(split1);
    merge_cb.requires(split2);
    merge_cb.ensures(merge);
    
    hist_class.add(create.method_decl(
        create.primitive_type(Sort.Void),
        split_cb.getContract(),
        "split",
        args,
        null
    ));
    hist_class.add(create.method_decl(
        create.primitive_type(Sort.Void),
        merge_cb.getContract(),
        "merge",
        args,
        null
    ));
    
  }
    
  private void add_begin_and_commit_to_class(Method m,boolean is_history) {
    // TODO Auto-generated method stub
    Type returns=create.primitive_type(Sort.Void);
    int N=m.getArity();
    DeclarationStatement args_short[]=new DeclarationStatement[2];
    DeclarationStatement args_long[]=new DeclarationStatement[2+N];
    ASTNode args[]=new ASTNode[N];
    args_short[0]=args_long[0]=create.field_decl("frac",create.primitive_type(Sort.Fraction));
    args_short[1]=args_long[1]=create.field_decl("proc",adt_type);
    for(int i=0;i<N;i++){
      args_long[i+2]=create.field_decl(m.getArgument(i),m.getArgType(i));
      args[i]=create.local_name(m.getArgument(i));
    }
    ContractBuilder begin_cb=new ContractBuilder();
    ContractBuilder commit_cb=new ContractBuilder();
    ASTNode proc=create.local_name("proc");
    ASTNode action_proc=create.invokation(null, null, "p_seq",create.invokation(null, null,"p_"+m.name,args), create.local_name("proc"));
    ASTNode proc_action=create.invokation(null, null, "p_seq", create.local_name("proc"),create.invokation(null, null,"p_"+m.name,args));
    begin_cb.requires(create.expression(StandardOperator.NEQ,create.local_name("frac"),create.reserved_name(ASTReserved.NoPerm)));
    begin_cb.ensures(create.expression(StandardOperator.NEQ,create.local_name("frac"),create.reserved_name(ASTReserved.NoPerm)));
    commit_cb.requires(create.expression(StandardOperator.NEQ,create.local_name("frac"),create.reserved_name(ASTReserved.NoPerm)));
    commit_cb.ensures(create.expression(StandardOperator.NEQ,create.local_name("frac"),create.reserved_name(ASTReserved.NoPerm)));
    begin_cb.requires(create.invokation(null, null,"hist_idle",create.local_name("frac"),is_history?proc:action_proc));
    begin_cb.ensures(create.invokation(null, null,"hist_do_"+m.name,create.local_name("frac"),proc));
    commit_cb.requires(create.invokation(null, null,"hist_do_"+m.name,create.local_name("frac"),proc));
    commit_cb.ensures(create.invokation(null, null,"hist_idle",create.local_name("frac"),is_history?proc_action:proc));
    Contract c=m.getContract();
    HashMap<NameExpression,ASTNode> old_map=new HashMap();
    HashMap<NameExpression,ASTNode> new_map=new HashMap();
    for(ASTNode n:c.modifies){
      String name=((FieldAccess)n).name;
      ASTNode mode=create.dereference(((FieldAccess)n).object, name+"_hist_mode");
      n=create.dereference(((FieldAccess)n).object, name+"_hist_value");
      old_map.put(create.field_name(name),create.unresolved_name(name+"_hist_act"));
      new_map.put(create.field_name(name),create.unresolved_name(name+"_hist_value"));
      ASTNode full=create.reserved_name(FullPerm);
      ASTNode nact=create.unresolved_name(name+"_hist_act");
      begin_cb.requires(create.expression(Perm,n,full));
      begin_cb.requires(create.expression(PointsTo,mode,full,create.constant(1)));
      begin_cb.ensures(create.expression(Perm,n,full));
      begin_cb.ensures(create.expression(PointsTo,mode,full,create.constant(2)));
      begin_cb.ensures(create.expression(EQ,n,create.expression(Old,n)));
      begin_cb.ensures(create.expression(Perm,nact,full));
      begin_cb.ensures(create.expression(EQ,n,nact));
      commit_cb.requires(create.expression(Perm,nact,full));
      commit_cb.requires(create.expression(Perm,n,full));
      commit_cb.requires(create.expression(PointsTo,mode,full,create.constant(2)));
      commit_cb.ensures(create.expression(Perm,n,full));
      commit_cb.ensures(create.expression(PointsTo,mode,full,create.constant(1)));
      commit_cb.ensures(create.expression(EQ,n,create.expression(Old,n)));
    }
    Simplify simp=new Simplify(this);
    Substitution sigma=new Substitution(source(),old_map);
    ApplyOld rw_old=new ApplyOld(sigma);
    Substitution rw_new=new Substitution(source(),new_map);
    commit_cb.requires(rw_new.rewrite(rw_old.rewrite(simp.rewrite(c.post_condition))));

    Method begin=create.method_decl(returns,begin_cb.getContract(), m.name+"_begin", args_long,null);
    Method commit=create.method_decl(returns,commit_cb.getContract(), m.name+"_commit", args_long,null);
    hist_class.add_dynamic(begin);
    hist_class.add_dynamic(commit);
    hist_class.add_dynamic(create.predicate("hist_do_"+m.name,null,args_short));
  }

  private ASTNode rebuild(ASTNode x,ASTNode y){
    if (x.isa(StandardOperator.Mult)){
      ASTNode lhs=((OperatorExpression)x).getArg(0);
      ASTNode rhs=((OperatorExpression)x).getArg(1);
      return create.invokation(null, null,"p_seq",rewrite(lhs),rebuild(rhs,y));
    } else {
      return create.invokation(null, null,"p_seq",rewrite(x),y);
    }
  }
  protected void add_lemma_to_adt(Method m) {
    DeclarationStatement args[]=rewrite(m.getArgs());
    Contract c=m.getContract();
    int N=m.getArity();
    ASTNode eq=c.post_condition;
    if (!eq.isa(EQ)){
      Abort("cannot generate axiom for %s",Configuration.getDiagSyntax().print(eq)); 
    }
    ASTNode lhs=((OperatorExpression)c.post_condition).getArg(0);
    ASTNode rhs=((OperatorExpression)c.post_condition).getArg(1);
    lhs=rebuild(lhs,create.local_name("p"));
    rhs=create.invokation(null, null,"p_seq",rewrite(rhs),create.local_name("p"));
    ASTNode [] arg_names = new ASTNode[N];
    for(int i=0;i<N;i++){
      arg_names[i]=create.local_name(m.getArgument(i));
    }
    eq=create.binder(
          Binder.FORALL,
          create.primitive_type(Sort.Boolean),
          rewrite(create.field_decl("p",adt_type),m.getArgs()),
          new ASTNode[][]{new ASTNode[]{lhs}},
          create.constant(true),
          create.expression(EQ,lhs,rhs)
      );
    adt.add_axiom(create.axiom(m.name+"_post",eq));
  }

  protected void add_process_to_adt(Method m) {
    DeclarationStatement args[]=rewrite(m.getArgs());
    ASTNode m_body=m.getBody();
    int N=m.getArity();
    ASTNode [] arg_names = new ASTNode[N];
    for(int i=0;i<N;i++){
      arg_names[i]=create.local_name(m.getArgument(i));
    }
    if (m_body!=null){
      ASTNode eq=create.expression(StandardOperator.EQ,
              rewrite(m.getBody()),
              create.invokation(null, null,"p_"+m.name , arg_names)
          );
      if(N>0){
        ASTNode trigger;
        if (m.getBody().isa(StandardOperator.Mult)){
          trigger=rewrite(m.getBody());
        } else {
          trigger=create.invokation(null, null,"p_"+m.name , arg_names);
        }
        eq=create.binder(
          Binder.FORALL,
          create.primitive_type(Sort.Boolean),
          copy_rw.rewrite(m.getArgs()),
          new ASTNode[][]{new ASTNode[]{trigger}},
          create.constant(true),
          eq
        );
      }
      adt.add_axiom(create.axiom(m.name+"_def_1",eq));
    }
    {
      ASTNode tmp=create.invokation(null, null,"p_"+m.name , arg_names);
      ASTNode lhs=create.invokation(null, null,"p_seq",create.local_name("p"),tmp);
      ASTNode rhs=create.invokation(null, null,"p_seq",create.local_name("p"),
          create.invokation(null, null,"p_seq",tmp,create.invokation(null, null,"p_empty")));
      ASTNode eq=create.binder(
          Binder.FORALL,
          create.primitive_type(Sort.Boolean),
          copy_rw.rewrite(create.field_decl("p",adt_type),m.getArgs()),
          new ASTNode[][]{new ASTNode[]{lhs}},
          create.constant(true),
          create.expression(EQ,lhs,rhs)
        );
      adt.add_axiom(create.axiom(m.name+"_def_2",eq));
    }
    adt.add_cons(create.function_decl(adt_type, null,"p_"+m.name,args,null));
  }
  
  @Override
  public void visit(MethodInvokation e){
    Method m=e.getDefinition();
    if (m.getReturnType().isPrimitive(Sort.Process)){
      result=create.invokation(null,null, "p_"+e.method,rewrite(e.getArgs()));
    } else {
      ASTNode in_args[]=e.getArgs();
      ASTNode args[]=new ASTNode[in_args.length];
      for(int i=0;i<in_args.length;i++){
        if (in_args[i].labels()>0 && in_args[i].isConstant(0)){
          args[i]=create.local_name(in_args[i].getLabel(0).getName());
        } else {
          args[i]=rewrite(in_args[i]);
        }
      }
      MethodInvokation res=create.invokation(rewrite(e.object), e.dispatch, e.method, args);
      res.set_before(rewrite(e.get_before()));
      res.set_after(rewrite(e.get_after()));
      result=res;
    }
  }
  
  @Override
  public void visit(NameExpression e){
    if (e.getKind()==NameExpression.Kind.Label){
      result=create.unresolved_name(e.getName());
    } else if (e.isReserved(ASTReserved.EmptyProcess)) {
      result=create.invokation(null, null, "p_empty");
    } else {
      super.visit(e);
    }
  }

  /*
  @Override
  public void visit(Method m){
    if (m.getReturnType().isPrimitive(Sort.Process)){
      Contract c=m.getContract();
      ContractBuilder cb = new ContractBuilder();
      for (ASTNode v:c.modifies){
        create.enter();
        create.setOrigin(v.getOrigin());
        cb.requires(create.expression(StandardOperator.Perm,rewrite(v),create.reserved_name(ASTReserved.FullPerm)));
        cb.ensures(create.expression(StandardOperator.Perm,rewrite(v),create.reserved_name(ASTReserved.FullPerm)));
        create.leave();
      }
      if (c.pre_condition!=null) cb.requires(rewrite(c.pre_condition));
      if (c.post_condition!=null) cb.ensures(rewrite(c.post_condition));
      add_process_to_adt(m);
      result=null;
    } else if (m.kind == Kind.Plain || m.kind== Kind.Constructor){
      ArrayList<DeclarationStatement> args=new ArrayList();
      Type returns=rewrite(m.getReturnType());
      ContractBuilder cb=new ContractBuilder();
      Contract c=m.getContract();
      cb.given(rewrite(c.given));
      cb.yields(rewrite(c.yields));
      for(DeclarationStatement decl:m.getArgs()){
        args.add(rewrite(decl));
      }
      for(ASTNode e:ASTUtils.conjuncts(c.pre_condition,StandardOperator.Star)){
        if (e.isa(StandardOperator.History)){
          NameExpression lbl=e.getLabel(0);
          cb.given(create.field_decl(lbl.getName(),create.class_type("Ref")));
          //args.add(create.field_decl(lbl.getName(),create.class_type("Ref")));
        }
        ASTNode tmp=rewrite(e);
        cb.requires(tmp);
      }
      for(ASTNode e:ASTUtils.conjuncts(c.post_condition,StandardOperator.Star)){
        if (e.isa(StandardOperator.History)){
          NameExpression lbl=e.getLabel(0);
          //cb.yields(create.field_decl(lbl.getName(),create.class_type("Ref")));
        }
        ASTNode tmp=rewrite(e);
        cb.ensures(tmp);
      }
      result=create.method_kind(m.kind,returns, cb.getContract(), m.name, args.toArray(new DeclarationStatement[0]), rewrite(m.getBody()));
    } else {
      super.visit(m);
    }
  }
  */

  private boolean isProcessRef(ASTNode n){
    String type=n.getType().toString();
    return type.equals("History")||type.equals("Future");
  }
  private boolean isHistoryRef(ASTNode n){
    String type=n.getType().toString();
    return type.equals("History");
  }
  private boolean isFutureRef(ASTNode n){
    String type=n.getType().toString();
    return type.equals("Future");
  }
  
  @Override
  public void visit(PrimitiveType t){
    if (t.sort==Sort.Process){
      result=adt_type;
    } else {
      super.visit(t);
    }
  }

  @Override
  public void visit(OperatorExpression e){
    switch(e.getOperator()){
    case AbstractState:{
      ASTNode data=rewrite(e.getArg(0));
      ASTNode half=create.expression(StandardOperator.Div,create.constant(1),create.constant(2));
      ASTClass cl=source().find((ClassType)e.getArg(0).getType());
      ArrayList<ASTNode> props=new ArrayList();
      HashMap<NameExpression,ASTNode> map=new HashMap();
      Substitution sigma=new Substitution(source(),map);
      for(DeclarationStatement decl:cl.dynamicFields()){
        props.add(create.expression(StandardOperator.Perm,
            create.dereference(data,decl.getName()+"_hist_init"),half));
        map.put(create.field_name(decl.getName()),
            create.dereference(data,decl.getName()+"_hist_init"));
      }
      props.add(rewrite(sigma.rewrite(e.getArg(1))));
      result=create.fold(StandardOperator.Star,props);
      return;
    }
    case Or:
      if(e.getType().isPrimitive(Sort.Process)){
        result=create.invokation(null,null,"p_merge",rewrite(e.getArguments()));
        return;
      }
      break;
    case Mult:
      if(e.getType().isPrimitive(Sort.Process)){
        result=create.invokation(null,null,"p_seq",rewrite(e.getArguments()));
        return;
      }
      break;
    case Future:
    case History:{
      ASTNode hist=e.getArg(0);
      ASTNode frac=e.getArg(1);
      ASTNode proc=e.getArg(2);
      result=create.invokation(rewrite(hist),null,"hist_idle",rewrite(frac),rewrite(proc));
      return;
    }
    case HistoryPerm:{
      if (e.getArg(0)instanceof FieldAccess){
        FieldAccess f=(FieldAccess)e.getArg(0);
        ASTNode frac=rewrite(e.getArg(1));
        if (isProcessRef(f.object)){
          ASTNode p1=create.expression(Perm,create.dereference(rewrite(f.object),f.name+"_hist_value"),frac);
          ASTNode p2=create.expression(PointsTo,create.dereference(rewrite(f.object),f.name+"_hist_mode"),
              frac,create.constant(1));
          result=create.expression(StandardOperator.Star,p1,p2);
        } else {
          throw new HREError("HPerm on non-history variable.");
        }
        return;
      }
      throw new HREError("HPerm on non-history variable.");
    }
    case Perm:{
      if (e.getArg(0)instanceof FieldAccess){
        FieldAccess f=(FieldAccess)e.getArg(0);
        ASTNode frac=rewrite(e.getArg(1));
        if (isProcessRef(f.object)){
          ASTNode p1=create.expression(Perm,create.dereference(rewrite(f.object),f.name+"_hist_value"),frac);
          ASTNode p2=create.expression(PointsTo,create.dereference(rewrite(f.object),f.name+"_hist_mode"),
              frac,create.constant(0));
          result=create.expression(StandardOperator.Star,p1,p2);
        } else {
          result=create.expression(Perm,create.dereference(rewrite(f.object),f.name),frac);
        }
        return;
      }
      break;
    }
    default:
      break;
    }
    super.visit(e);
  }
  
  protected boolean in_action=false;
  
  @Override
  public void visit(ActionBlock ab){
    if (in_action){
      Fail("nested action block");
    }
    in_action=true;
    MethodInvokation act=(MethodInvokation)ab.action;
    ASTNode hist=rewrite(ab.history);
    ASTNode frac=rewrite(ab.fraction);
    ASTNode p_expr=rewrite(ab.process);
    p_expr.clearLabels();
    ArrayList<ASTNode> args=new ArrayList<ASTNode>();
    args.add(frac);
    args.add(p_expr);
    for(ASTNode n:act.getArgs()){
      args.add(rewrite(n));
    }
    BlockStatement res=create.block();
    res.add(create.invokation(hist, null, act.method+"_begin", args.toArray(new ASTNode[0])));
    res.add(rewrite(ab.block));
    res.add(create.invokation(hist, null, act.method+"_commit", args.toArray(new ASTNode[0])));
    result=res;
    in_action=false;
  }
  
  @Override
  public void visit(ASTSpecial s){
    switch(s.kind){
    case SplitHistory:{
      ASTNode hist=s.args[0];
      ASTNode args[]=new ASTNode[4];
      for(int i=0;i<4;i++){
        args[i]=rewrite(s.args[i+1]);
      }
      result=create.invokation(rewrite(hist), null , "split", args);
      break;
    }
    case MergeHistory:{
      ASTNode hist=s.args[0];
      ASTNode args[]=new ASTNode[4];
      for(int i=0;i<4;i++){
        args[i]=rewrite(s.args[i+1]);
      }
      result=create.invokation(rewrite(hist), null , "merge", args);
      break;
    }
    case CreateHistory:{
      ASTNode hist=rewrite(s.args[0]);
      result=create.invokation(hist, null , "begin_hist");
      break;
    }
    case CreateFuture:{
      setUpEffect(s);
      break;
    }
    case DestroyFuture:{
      ASTNode future=rewrite(s.args[0]);
      result=create.invokation(future, null , "end_future");
      break; 
    }
    case DestroyHistory:{
      setUpEffect(s);
      break;
    }
    default:
        super.visit(s);
        break;
    }
  }

  private void setUpEffect(ASTSpecial s) {
    ASTNode model=s.args[0];
    boolean hist=isHistoryRef(model);
    String name=(hist?"end_hist_":"begin_future_")+count.incrementAndGet();
    ASTNode proc=s.args[1];
    if (!(proc instanceof MethodInvokation)){
      Fail("second argument of %s must be a defined process",hist?"destroy":"create");
    }
    MethodInvokation effect=(MethodInvokation)proc;
    
    
    
    ClassType ct=(ClassType)model.getType();
    if (ct==null){
      Abort("type of %s is null",Configuration.getDiagSyntax().print(model));
    }
    ASTClass cl=source().find(ct);
    
    
    Method def=effect.getDefinition();
    
    Method end_hist;
    
    final HashMap<String,ASTNode> map=new HashMap();
    final HashMap<String,ASTNode> new_map=new HashMap();
    AbstractRewriter sigma=new AbstractRewriter(source()){
      @Override
      public void visit(Dereference d){
        ASTNode n=map.get(d.field);
        if (n==null){
          super.visit(d);
        } else {
          result=copy_rw.rewrite(n);
        }
      }
      @Override
      public void visit(FieldAccess d){
        ASTNode n=map.get(d.name);
        if (n==null){
          super.visit(d);
        } else {
          result=copy_rw.rewrite(n);
        }
      }
    };
    AbstractRewriter new_sigma=new AbstractRewriter(source()){
      @Override
      public void visit(Dereference d){
        ASTNode n=new_map.get(d.field);
        if (n==null){
          super.visit(d);
        } else {
          result=copy_rw.rewrite(n);
        }
      }
      @Override
      public void visit(FieldAccess d){
        ASTNode n=new_map.get(d.name);
        Warning("name %s",d.name);
        if (n==null){
          super.visit(d);
        } else {
          result=copy_rw.rewrite(n);
        }
      }
    };
    ApplyOld rename_old=new ApplyOld(sigma);
    ContractBuilder cb=new ContractBuilder();
    for(DeclarationStatement d:cl.dynamicFields()){
      map.put(d.name,create.expression(Old,create.field_name(d.name+(hist?"_hist_init":"_hist_value"))));
      new_map.put(d.name,create.field_name(d.name+(hist?"_hist_value":"_hist_init")));
      cb.requires(create.expression(Perm,create.field_name(d.name+"_hist_value"),create.reserved_name(FullPerm)));
      cb.requires(create.expression(PointsTo,create.field_name(d.name+"_hist_mode"),
          create.reserved_name(FullPerm),create.constant(hist?1:0)));
      cb.requires(create.expression(Perm,create.field_name(d.name+"_hist_init"),create.reserved_name(FullPerm)));
      cb.ensures(create.expression(Perm,create.field_name(d.name+"_hist_value"),create.reserved_name(FullPerm)));
      cb.ensures(create.expression(PointsTo,create.field_name(d.name+"_hist_mode"),
          create.reserved_name(FullPerm),create.constant(hist?0:1)));
      cb.ensures(create.expression(Perm,create.field_name(d.name+"_hist_init"),create.reserved_name(FullPerm)));
      if(hist){
        cb.ensures(create.expression(Perm,create.field_name(d.name+"_hist_act"),create.reserved_name(FullPerm)));
      } else {
        cb.requires(create.expression(Perm,create.field_name(d.name+"_hist_act"),create.reserved_name(FullPerm)));
      }
      cb.ensures(create.expression(EQ
          , create.field_name(d.name+"_hist_value")
          , create.expression(Old,create.field_name(d.name+"_hist_value"))
      ));
    }
    Simplify simp=new Simplify(this);
    cb.ensures(new_sigma.rewrite(rename_old.rewrite(def.getContract().post_condition)));
    
    ArrayList<ASTNode> def_names=new ArrayList();
    for(DeclarationStatement d:def.getArgs()){
      def_names.add(create.local_name(d.name));
    }
    
    ASTNode tmp=create.invokation(null, null, "hist_idle",
        create.reserved_name(ASTReserved.FullPerm),
        create.invokation(null,null,"p_"+effect.method,def_names)
    );
    if (hist){ cb.requires(tmp); } else { cb.ensures(tmp); }

    
    end_hist=create.method_decl(
        create.primitive_type(Sort.Void),
        cb.getContract(),
        name,
        rewrite(def.getArgs()),
        null
    );
    hist_class.add_dynamic(end_hist);
    System.out.printf("%s%n",Configuration.getDiagSyntax().print(end_hist));

    result=create.invokation(rewrite(model), null ,name,rewrite(effect.getArgs()));
  }
  
  @Override
  public void visit(FieldAccess a){
    if (a.object!=null && a.object.getType()!=null && isProcessRef(a.object)){
      String prefix=in_action?"hist_":"free_";
      if (a.value==null){
        //result=create.invokation(rewrite(a.object),null,prefix+"get_"+a.name);
        result=create.dereference(rewrite(a.object),a.name+"_hist_value");
      } else {
        result=create.invokation(rewrite(a.object),null,prefix+"set_"+a.name,rewrite(a.value));
      }
    } else {
      result=create.dereference(rewrite(a.object),a.name);
      if (a.value!=null){
        result=create.assignment(result,rewrite(a.value));
      }
    }
  }

  /**
   * This method determines the classes that have to be rewritten first.
   * @param d
   * @return
   */
  private boolean high_prio(ASTDeclaration d){
    return (d instanceof AxiomaticDataType)||d.name.equals("History")||d.name.equals("Future");
  }
  
  @Override
  public ProgramUnit rewriteAll(){
    for(ASTDeclaration d:source().get()){
      if(high_prio(d)){
        ASTDeclaration tmp=rewrite(d);
        if(tmp!=null) target().add(tmp);
      }
    }
    for(ASTDeclaration d:source().get()){
      if(!high_prio(d)){
        ASTDeclaration tmp=rewrite(d);
        if(tmp!=null) target().add(tmp);
      }
    }
    target().index_classes();
    return target();
  }

}
