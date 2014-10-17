package vct.col.rewrite;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;

import vct.col.ast.BindingExpression.Binder;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.*;
import vct.col.util.ASTUtils;
import vct.util.Configuration;
import static vct.col.ast.StandardOperator.Perm;


public class CheckHistoryAlgebra extends AbstractRewriter {

  public CheckHistoryAlgebra(ProgramUnit source) {
    super(source);
  }

  private Hashtable<String,String> composite_map;
  private Hashtable<String,Method> process_map;
  
  private Type adt_type;
  private AxiomaticDataType adt;

  @Override
  public void visit(ASTClass cl){
    composite_map=new Hashtable<String,String>();
    process_map=new Hashtable<String,Method>();
    adt=create.adt("Process");
    adt_type=create.class_type("Process");
    DeclarationStatement proc_p1=create.field_decl("p1", adt_type);
    DeclarationStatement proc_p2=create.field_decl("p2", adt_type);
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
    currentTargetUnit.add(adt);
    HashSet<NameExpression> hist_set=new HashSet<NameExpression>();
    for(Method m:cl.dynamicMethods()){
      if (!m.getReturnType().isPrimitive(Sort.Process)) continue;
      ASTNode body=m.getBody();
      process_map.put(m.name, m);
      for(ASTNode n:m.getContract().modifies){
        hist_set.add((NameExpression)n);
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
    
    res.add(create.predicate("hist_idle", create.constant(true), new DeclarationStatement[]{create.field_decl("p",adt_type)}));
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
      begin_args.add(create.field_decl("p", adt_type));
      begin_cb.requires(create.invokation(null,null,"hist_idle",create.local_name("p")));
      begin_cb.ensures(create.invokation(null,null,"hist_"+m.name,create.local_name("p")));
      commit_args.add(create.field_decl("p", adt_type));
      commit_cb.requires(create.invokation(null,null,"hist_"+m.name,create.local_name("p")));
      commit_cb.ensures(create.invokation(null,null,"hist_idle",
          create.invokation(null,null,"p_seq",create.local_name("p"),
              create.invokation(null,null,"p_"+m.name))));
      HashMap<NameExpression,ASTNode> old_map=new HashMap();
      for(ASTNode n:c.modifies){
        NameExpression name=(NameExpression)n;
        NameExpression name_old=create.field_name(name.getName()+"_old");
        mod_set.add(name);
        old_map.put(name,name_old);
        ASTNode half=create.expression(StandardOperator.Div,create.constant(1),create.constant(2));
        ASTNode full=create.reserved_name(ASTReserved.FullPerm);
        begin_cb.requires(create.expression(Perm,name,full));
        begin_cb.ensures(create.expression(Perm,name,full));
        begin_cb.ensures(create.expression(StandardOperator.EQ,name,create.expression(StandardOperator.Old,name)));
        begin_cb.ensures(create.expression(Perm,name_old,half));
        begin_cb.ensures(create.expression(StandardOperator.EQ,name,name_old));
        commit_cb.requires(create.expression(Perm,name,full));
        commit_cb.ensures(create.expression(Perm,name,full));
        commit_cb.ensures(create.expression(StandardOperator.EQ,name,create.expression(StandardOperator.Old,name)));
        commit_cb.requires(create.expression(Perm,name_old,half));
      }
      Substitution sigma=new Substitution(source(),old_map);
      ApplyOld rw_old=new ApplyOld(sigma);
      commit_cb.requires(rw_old.rewrite(c.post_condition));
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
      res.add(create.predicate("hist_"+m.name, create.constant(true), new DeclarationStatement[]{create.field_decl("p",adt_type)}));
      create.leave();
    }
    result=res;
  }
  
  @Override
  public void visit(MethodInvokation e){
    Method m=e.getDefinition();
    if (m.getReturnType().isPrimitive(Sort.Process)){
      result=create.invokation(null,null, "p_"+e.method,rewrite(e.getArgs()));
    } else {
      super.visit(e);
    }
  }
  
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
      DeclarationStatement args[]=rewrite(m.getArgs());
      ASTNode m_body=m.getBody();
      if (m_body!=null){
        int N=m.getArity();
        ASTNode [] arg_names = new ASTNode[N];
        for(int i=0;i<N;i++){
          arg_names[i]=create.local_name(m.getArgument(i));
        }
        ASTNode eq=create.binder(
            Binder.FORALL,
            create.primitive_type(Sort.Boolean),
            copy_rw.rewrite(m.getArgs()),
            create.constant(true),
            create.expression(StandardOperator.EQ,
                rewrite(m.getBody()),
                create.invokation(null, null,"p_"+m.name , arg_names)
            )
        );
        adt.add_axiom(create.axiom(m.name+"_def",eq));
      }
      adt.add_cons(create.function_decl(adt_type, null,"p_"+m.name,args,null));
      result=null;
    } else {
      /*
      ArrayList<DeclarationStatement> args=new ArrayList();
      Type returns=rewrite(m.getReturnType());
      ContractBuilder cb=new ContractBuilder();
      Contract c=m.getContract();
      for(DeclarationStatement decl:m.getArgs()){
        args.add(rewrite(decl));
      }
      for(ASTNode e:ASTUtils.conjuncts(c.pre_condition,StandardOperator.Star)){
        if (e.isa(StandardOperator.History)){
          NameExpression lbl=e.getLabel(0);
          args.add(create.field_decl(lbl.getName(),create.class_type("Ref")));
        }
        ASTNode tmp=rewrite(e);
        cb.requires(tmp);
      }
      for(ASTNode e:ASTUtils.conjuncts(c.pre_condition,StandardOperator.Star)){
        ASTNode tmp=rewrite(e);
        cb.ensures(tmp);
      }
      result=create.method_kind(m.kind,returns, cb.getContract(), m.name, args.toArray(new DeclarationStatement[0]), rewrite(m.getBody()));
      */
      super.visit(m);
    }
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
    case History:{
      NameExpression lbl=e.getLabel(0);
      result=create.invokation(create.unresolved_name(lbl.getName()),null,"hist_idle",rewrite(e.getArguments()));
      auto_labels=false;
      return;
    }
    default:
      break;
    }
    super.visit(e);
  }
  
  @Override
  public void visit(ActionBlock ab){
    MethodInvokation act=(MethodInvokation)ab.action;
    NameExpression lbl=ab.process.getLabel(0);
    lbl=create.unresolved_name(lbl.getName());
    ASTNode p_expr=rewrite(ab.process);
    p_expr.clearLabels();
    BlockStatement res=create.block();
    res.add(create.invokation(lbl, null, act.method+"_begin", p_expr));
    res.add(rewrite(ab.block));
    res.add(create.invokation(lbl, null, act.method+"_commit", p_expr));
    result=res;
  }
}
