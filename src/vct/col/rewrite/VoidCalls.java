package vct.col.rewrite;

import static hre.System.*;

import java.util.HashMap;

import vct.col.ast.ASTFlags;
import vct.col.ast.ASTNode;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.ProgramUnit;
import vct.col.ast.ReturnStatement;

public class VoidCalls extends AbstractRewriter {

  public VoidCalls(ProgramUnit source) {
    super(source);
  }
  
  public void visit(Method m){
    switch(m.kind){
    case Predicate:
    case Pure:
      result=copy_rw.rewrite(m);
      return;
    default:
      break;
    }   
    if (m.getReturnType().isVoid()){
      super.visit(m);
    } else {
      DeclarationStatement m_args[]=m.getArgs();
      int N=m_args.length;
      DeclarationStatement args[]=new DeclarationStatement[N+1];
      args[0]=new DeclarationStatement("__result",rewrite(m.getReturnType()));
      args[0].setOrigin(m);
      args[0].setFlag(ASTFlags.OUT_ARG, true);
      for(int i=0;i<N;i++){
        args[i+1]=rewrite(m_args[i]);
      }

      ContractBuilder cb=new ContractBuilder();
      Contract c=m.getContract();
      if(c!=null){
        HashMap<NameExpression,ASTNode>map=new HashMap<NameExpression,ASTNode>();
        map.put(create.reserved_name("\\result"),create.local_name("__result"));
        Substitution subst=new Substitution(source(),map);
        cb.requires(c.pre_condition.apply(subst));
        cb.ensures(c.post_condition.apply(subst));
        if (c.given!=null){
          cb.given(rewrite(c.given));
        }
        if (c.yields!=null){
          cb.yields(rewrite(c.yields));
        }
      }
      result=create.method_decl(
          create.primitive_type(PrimitiveType.Sort.Void),
          cb.getContract(),
          m.getName(),
          args,
          rewrite(m.getBody()));
    }
  }
  
  public void visit(ReturnStatement s){
    ASTNode res=s.getExpression();
    if (res!=null){
      result=create.block(
          create.assignment(create.local_name("__result"),rewrite(res)),
          create.return_statement()
      );
    } else {
      super.visit(s);
    }
  }
  
  public void visit(MethodInvokation e){
    Method m=e.getDefinition();
    if (m==null) Abort("unexpected null method definition at %s",e.getOrigin());
    switch(m.kind){
    case Predicate:
    case Pure:
      super.visit(e);
      return;
    default:
      break;
    }
    if (!m.getReturnType().isVoid()){
      Fail("unexpected non-void method invokation at %s",e.getOrigin());
    }
    super.visit(e);
  }
  
  public void visit(AssignmentStatement s){
    if (s.getExpression() instanceof MethodInvokation){
      MethodInvokation e=(MethodInvokation)s.getExpression();
      Method m=e.getDefinition();
      if (e==null) Abort("cannot process invokation of %s without definition",e.method);
      if (m.kind==Method.Kind.Plain){
        int N=e.getArity();
        ASTNode args[]=new ASTNode[N+1];
        args[0]=rewrite(s.getLocation());
        for(int i=0;i<N;i++){
          args[i+1]=rewrite(e.getArg(i));
        }
        args[0]=rewrite(s.getLocation());
        MethodInvokation res=create.invokation(rewrite(e.object), rewrite(e.dispatch) , e.method , args );
        for(NameExpression lbl:e.getLabels()){
          Debug("VOIDCALLS: copying label %s",lbl);
          res.addLabel(rewrite(lbl));
        }
        res.set_before(rewrite(e.get_before()));
        res.set_after(rewrite(e.get_after()));
        result=res;
        return;
      }
    }
    super.visit(s);
  }
}
