package vct.col.rewrite;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.concurrent.atomic.AtomicInteger;

import vct.col.ast.*;

public class CSLencoder extends AbstractRewriter {

  public CSLencoder(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(ASTClass cl){
    String name=cl.getName();
    if (name.startsWith("Atomic")){
      ASTClass res=create.ast_class(name, ASTClass.ClassKind.Plain,null, null,null);
      for(DeclarationStatement decl:cl.dynamicFields()){
        res.add_dynamic(rewrite(decl));
      }
      for(Method m:cl.dynamicMethods()){
        if (m.kind==Method.Kind.Constructor){
          res.add_dynamic(rewrite(m));
        }
      }
      result=res;
    } else {
      super.visit(cl);
    }
  }

  private boolean has_csl_inv(ASTClass cl){
    for(Method m:cl.dynamicMethods()){
      if (m.name.equals("csl_invariant")){
        return true;
      }
    }
    return false;
  }
  
  @Override
  public void visit(Method m){
    if(m.kind==Method.Kind.Constructor && has_csl_inv((ASTClass)m.getParent())){
      Method.Kind kind=Method.Kind.Constructor;
      ContractBuilder cb=new ContractBuilder();
      rewrite(m.getContract(),cb);
      cb.ensures(create.invokation(null,null,"csl_invariant"));
      String name=m.name;
      DeclarationStatement args[]=rewrite(m.getArgs());
      BlockStatement body;
      if (m.getBody()!=null){
        body=(BlockStatement)rewrite(m.getBody());
        body.add_statement(create.expression(StandardOperator.Fold,
            create.invokation(null,null,"csl_invariant")
        ));   
      } else {
        body=null;
      }
      Contract contract=cb.getContract();
      Type returns=rewrite(m.getReturnType());
      result=create.method_kind(kind, returns, contract, name, args, m.usesVarArgs(), body);
    } else {
      super.visit(m);
    }
  }
  
  private AtomicInteger count=new AtomicInteger();
  
  @Override
  public void visit(MethodInvokation e){
    Method m=e.getDefinition();
    boolean replace=false;
    ASTNode decl=m.getParent();
    if(decl instanceof ASTClass){
      ASTClass cl=(ASTClass)decl;
      String name=cl.getName();
      if (name.startsWith("Atomic")){
        replace=true;
      }
    }
    if(replace){
      switch(m.getKind()){
      case Constructor:
        super.visit(e);
        return;
      case Plain:
        break;
      default:
        Fail("Atomic classes can only use constructors and plain methods!");
        return;
      }
      int no=count.incrementAndGet();
      String result_name="csl_result_"+no;
      String return_label="csl_return_"+no;
      ArrayList<ASTNode> subjects=new ArrayList();
      for(ASTNode node:e.get_before()){
        if (node.isSpecial(ASTSpecial.Kind.CSLSubject)){
          subjects.add(((ASTSpecial)node).args[0]);
        }
      }
      if (subjects.size()==0){
        //Warning("no explicit subjects for atomic method call.");
        subjects.add(create.reserved_name(ASTReserved.This));
      }
      BlockStatement block=create.block();
      if (!m.getReturnType().isVoid()){
        currentBlock.add(create.field_decl(result_name,rewrite(m.getReturnType())));
      }
      /*
      for(ASTNode node:subjects){
        block.add(create.special(ASTSpecial.Kind.Inhale,create.invokation(rewrite(node),null,"csl_invariant")));
        block.add(create.expression(StandardOperator.Unfold,create.invokation(rewrite(node),null,"csl_invariant")));
      }
      */
      for(ASTNode s:e.get_before()){
        if (s.isSpecial(ASTSpecial.Kind.Transfer)){
          Warning("ignoring transfer statement at %s",s.getOrigin());
        } else if (s.isSpecial(ASTSpecial.Kind.CSLSubject)){
          // skip
        } else {
          block.add(rewrite(s));
        }
      }
      InlineMethod inline=new InlineMethod(source());
      inline.inline(block,result_name,return_label,m,e.object,e.getArgs(),e.getOrigin());    
      block.add(create.special(ASTSpecial.Kind.Label,create.label(return_label)));
      Hashtable map=new Hashtable();
      Substitution sigma=new Substitution(source(),map);
      map.put(create.reserved_name(ASTReserved.Result),create.local_name(result_name));
      for(ASTNode s:e.get_after()){
        if (s.isSpecial(ASTSpecial.Kind.Transfer)){
          // skip
        } else {
          block.add(sigma.rewrite(rewrite(s)));
        }
      }
      /*
      for(ASTNode node:subjects){
        block.add(create.expression(StandardOperator.Fold,create.invokation(rewrite(node),null,"csl_invariant")));
        block.add(create.special(ASTSpecial.Kind.Exhale,create.invokation(rewrite(node),null,"csl_invariant")));
      }
      */
      currentBlock.add(create.csl_atomic(block,subjects.toArray(new ASTNode[0])));
      if (m.getReturnType().isVoid()){
        result=create.comment("// dummy");
      } else {
        result=create.local_name(result_name);
      }
    } else {
      super.visit(e);
    }
    
  }
  
  
}
