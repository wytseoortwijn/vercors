package vct.col.rewrite;

import static hre.System.Fail;
import static hre.System.Warning;
import hre.HREError;
import hre.ast.MessageOrigin;
import hre.ast.Origin;
import hre.lang.Ref;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import vct.col.ast.*;
import vct.col.util.ASTFactory;
import vct.col.util.ASTUtils;
import vct.util.Configuration;

class RewriteRule {
  public final String name;
  public final Set<String> vars;
  public final ASTNode lhs;
  public final ASTNode rhs;
  public RewriteRule(String name,Set<String> vars,ASTNode lhs,ASTNode rhs){
    this.name=name;
    this.vars=vars;
    this.lhs=lhs;
    this.rhs=rhs;
  }
}

class MatchLinear implements ASTMapping1<Boolean,ASTNode> {
  
  public Hashtable<String,Ref<ASTNode>> match=new Hashtable<String, Ref<ASTNode>>();
  
  public MatchLinear(Set<String> vars){
    for(String name:vars){
      match.put(name,new Ref<ASTNode>());
    }
  }

  @Override
  public void pre_map(ASTNode n, ASTNode a) {
    // TODO Auto-generated method stub
  }

  @Override
  public Boolean post_map(ASTNode n, Boolean res, ASTNode a) {
    if (res==null) throw new HREError("cannot match %s",n.getClass());
    return res;
  }

  @Override
  public Boolean map(StandardProcedure p, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(ConstantExpression e, ASTNode a) {
    return a.isConstant(e);
  }

  @Override
  public Boolean map(OperatorExpression e1, ASTNode a) {
    if (e1.isa(StandardOperator.IndependentOf)){
      ASTNode tmp = match.get(((NameExpression)e1.getArg(1)).getName()).get();
      if (tmp instanceof DeclarationStatement){
        DeclarationStatement decl=(DeclarationStatement)tmp;
        return !ASTUtils.find_name(a,decl.name) && e1.getArg(0).apply(this,a);
      } else {
        return false;
      }
    }
    if (a.isa(e1.getOperator())){
      OperatorExpression e2=(OperatorExpression)a;
      ASTNode[] args1=e1.getArguments();
      ASTNode[] args2=e2.getArguments();
      if (args1.length!=args2.length) return false;
      for(int i=0;i<args1.length;i++){
        if (!args1[i].apply(this,args2[i])){
          return false;
        }
      }
      return true;
    } else {
      return false;
    }
  }

  @Override
  public Boolean map(NameExpression e, ASTNode a) {
    String name=e.getName();
    Ref<ASTNode> ref=match.get(name);
    if(ref==null){
      return a.isName(name);
    } else if (ref.get()==null) {
      ref.set(a);
      return true;
    } else {
      if (ref.get() instanceof DeclarationStatement){
        DeclarationStatement dref=(DeclarationStatement)ref.get();
        return a.isName(dref.name);
      }
      return ref.get().match(a);
      //throw new HREError("non-linear left-hand side");
    }
  }

  @Override
  public Boolean map(ClassType t, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(FunctionType t, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(PrimitiveType t, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(RecordType t, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(MethodInvokation e, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(BlockStatement s, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(IfStatement s, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(ReturnStatement s, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(AssignmentStatement s, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(DeclarationStatement s, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(LoopStatement s, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(Method m, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(ASTClass c, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(ASTWith astWith, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(BindingExpression e, ASTNode a) {
    if (e.getDeclCount()!=1) throw new HREError("binders must declare precisely one variable");
    DeclarationStatement decl=e.getDeclaration(0);
    String name=decl.getName();
    Ref<ASTNode> ref=match.get(name);
    if(ref==null){
      throw new HREError("bound variable must be a matched variable");
    } else if (ref.get()==null) {
      if (!(a instanceof BindingExpression)) return false;
      BindingExpression ee=(BindingExpression)a;
      if (ee.getDeclCount()!=1) return false;
      DeclarationStatement ee_decl=ee.getDeclaration(0);
      Warning("attempting %s -> %s",name,ee_decl.name);
      ref.set(ee_decl);
      if (ee.binder!=e.binder) return false;
      return e.select.apply(this,ee.select) && e.main.apply(this,ee.main);
    } else {
      throw new HREError("non-linear left-hand side");
    }

  }

  @Override
  public Boolean map(Dereference e, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(Lemma lemma, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(ParallelBarrier parallelBarrier, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(ParallelBlock parallelBlock, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(Contract contract, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(ASTSpecial special, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(VariableDeclaration variableDeclaration, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(TupleType tupleType, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(AxiomaticDataType adt, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(Axiom axiom, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(Hole hole, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(ActionBlock actionBlock, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(ASTSpecialDeclaration s, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(TypeExpression t, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Boolean map(ForEachLoop s, ASTNode a) {
    // TODO Auto-generated method stub
    return null;
  }
  
}

class MatchSubstitution extends AbstractRewriter {

  public Hashtable<String,Ref<ASTNode>> match;
  
  public MatchSubstitution(Hashtable<String, Ref<ASTNode>> match) {
    super(null,null);
    this.match=match;
  }
  
  @Override
  public void visit(NameExpression e){
    String name=e.getName();
    Ref<ASTNode> ref=match.get(name);
    if(ref==null){
      super.visit(e);
    } else {
      ASTNode n=ref.get();
      if (n instanceof DeclarationStatement){
        DeclarationStatement dref=(DeclarationStatement)n;
        result=create.local_name(dref.name);
      } else {
        result=copy_rw.rewrite(n);
      }
    }
  }
  
  AtomicInteger ai=new AtomicInteger();
  
  @Override
  public void visit(BindingExpression e){
    DeclarationStatement decls[]=e.getDeclarations();
    for(int i=0;i<decls.length;i++){
      Ref<ASTNode> ref=match.get(decls[i].name);
      DeclarationStatement dref;
      if(ref==null) {
        int no=ai.getAndIncrement();
        dref=create.field_decl(decls[i].name+"_rw_"+no,decls[i].getType()); 
        match.put(decls[i].name,new Ref<ASTNode>(dref));
      } else {
        dref=(DeclarationStatement)ref.get();
      }
      decls[i]=create.field_decl(dref.name,rewrite(dref.getType()),rewrite(decls[i].getInit()));
    }
    if (e.binder==BindingExpression.Binder.LET){
      HashMap<NameExpression, ASTNode> map=new HashMap<NameExpression, ASTNode>();
      for(int i=0;i<decls.length;i++){
        map.put(create.local_name(decls[i].name),rewrite(decls[i].getInit()));
      }
      Substitution sigma=new Substitution(source(),map);
      ASTNode tmp=rewrite(e.main);
      ASTNode res=sigma.rewrite(tmp);
      result=res;
    } else {
      result=create.binder(e.binder,rewrite(e.result_type),decls,rewrite(e.select),rewrite(e.main));
    }
  }
   
}

class Normalizer extends AbstractRewriter {

  private RewriteSystem trs;
  
  public Normalizer(ProgramUnit source,RewriteSystem trs) {
    super(source);
    this.trs=trs;
  }
  
  @Override
  public void post_visit(ASTNode node){
    Ref<ASTNode> ref=new Ref<ASTNode>(result);
    boolean again=(node instanceof ExpressionNode) && trs.step(ref);
    super.post_visit(node);
    if(again){
      result=rewrite(ref.get());
    } else {
      result=ref.get();
    }
  }

}

public class RewriteSystem {

  public ProgramUnit normalize(ProgramUnit pu){
    Normalizer n=new Normalizer(pu,this);
    return n.rewriteAll();
  }
  
  private ArrayList<RewriteRule> rules=new ArrayList<RewriteRule>();
  
  private AbstractRewriter normalize;
  
  public boolean step(Ref<ASTNode> term){
    for(RewriteRule rule:rules){
      //Configuration.getDiagSyntax().print(System.err, rule.lhs);
      MatchLinear matcher=new MatchLinear(rule.vars);
      if (rule.lhs.apply(matcher,term.get())){
        MatchSubstitution sigma=new MatchSubstitution(matcher.match);
        //System.err.println(" match");
        term.set(sigma.rewrite(rule.rhs));
        return true;
      }
      //System.err.println(" no match");
    }
    return false;
  }
  
  public RewriteSystem(ProgramUnit pu,String sys){
    Origin o=new MessageOrigin("rewrite system "+sys);
    normalize=new AbstractRewriter(pu){
      @Override
      public void post_visit(ASTNode node){
        Ref<ASTNode> ref=new Ref<ASTNode>(result);
        boolean again=step(ref);
        super.post_visit(node);
        if(again){
          result=rewrite(ref.get());
        }
      }
    };
    HashSet<String> vars=new HashSet<String>();
    for(ASTNode d:pu.find(sys)){
      if(d instanceof DeclarationStatement){
        DeclarationStatement decl=(DeclarationStatement)d;
        String name=decl.getName();
        //Warning("variable %s",name);
        vars.add(name);
      }
    }
    for(ASTNode d:pu.find(sys)){
      if (d instanceof Axiom){
        Axiom axiom=(Axiom)d;
        //Warning("axiom %s",axiom.name);
        if (!axiom.getRule().isa(StandardOperator.EQ)){
          Fail("not a == rule");
        }
        ASTNode lhs=((OperatorExpression)axiom.getRule()).getArg(0);
        ASTNode rhs=((OperatorExpression)axiom.getRule()).getArg(1);
        rules.add(new RewriteRule(axiom.name,vars,lhs,rhs));
        continue;
      }
    }

  }

  public ASTNode normalize(ASTNode tmp) {
    return normalize.rewrite(tmp);
  }
}
