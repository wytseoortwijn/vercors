package vct.antlr4.parser;


import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTSpecial;
import vct.col.ast.BeforeAfterAnnotations;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.rewrite.AbstractRewriter;

public class JavaPostProcessor extends AbstractRewriter {

  private int wildcard_count=0;
  
  public JavaPostProcessor(ProgramUnit source) {
    super(source);
  }

  @Override
  public void visit(ASTSpecial s){
    switch(s.kind){
    case Expression:
      result=rewrite(s.args[0]);
      break;
    default:
      super.visit(s);
      break;
    }
  }
  
  @Override
  public void visit(ClassType t){
    String name[]=t.getNameFull();
    if (name.length==1 && name[0].equals("seq")){
      result=create.primitive_type(PrimitiveType.Sort.Sequence,t.getArgs());
    } else {
      super.visit(t);
    }
  }
  
  @Override
  public void visit(ASTClass c){
    super.visit(c);
    ASTClass decl=(ASTClass)result;
    int N=0;
    for(Method m:decl.dynamicMethods()){
      if (m.kind==Method.Kind.Constructor) N++;
    }
    if (N==0) create.addZeroConstructor(decl);
  }

  @Override
  public void visit(Method m){
    if (m.getReturnType().isPrimitive(PrimitiveType.Sort.Resource)){
      result=create.predicate(m.getName(), rewrite(m.getBody()), rewrite(m.getArgs()));
    } else {
      super.visit(m);
    }
  }
  
  @Override
  public void visit(MethodInvokation e){
    if (e.object==null){
      StandardOperator op=null;
      switch(e.method){
      case "head":
        op=StandardOperator.Head;
        break;
      case "tail":
        op=StandardOperator.Tail;
        break;
      }
      if (op!=null){
        result=create.expression(op,rewrite(e.getArgs()));
        return;
      }
    }
    result=process_with_then(create.invokation(rewrite(e.object), e.dispatch, e.method, rewrite(e.getArgs())),e);
  }
  
  private <T extends ASTNode & BeforeAfterAnnotations> ASTNode process_with_then(T dst,T src) {
    for(ASTNode n:src.get_before()){
      dst.get_before().add(rewrite(n));
    }
    for(ASTNode n:src.get_after()){
      if (n.isSpecial(ASTSpecial.Kind.Label)) {
    	String label=((NameExpression)((ASTSpecial)n).args[0]).getName();
    	dst.labeled(label);
      } else if (n.isSpecial(ASTSpecial.Kind.With)) {
        for(ASTNode w : ((BlockStatement)((ASTSpecial)n).args[0])){
          dst.get_before().add(rewrite(w));
        }
      } else if (n.isSpecial(ASTSpecial.Kind.Then)){
        for(ASTNode w : ((BlockStatement)((ASTSpecial)n).args[0])){
          dst.get_after().add(rewrite(w));
        }
      } else {
        dst.get_after().add(rewrite(n));
      }
    }
    return dst;
  }

  public void visit(NameExpression n){
    if (n.getName().equals("?")){
      wildcard_count++;
      String name="wildcard_"+wildcard_count;
      if (currentContractBuilder==null) Abort("no contract builder set");
      currentContractBuilder.given(create.field_decl(name, create.primitive_type(Sort.Class),create.class_type("Object")));
      result=create.unresolved_name(name);
      return;
    } else {
      super.visit(n);
    }
  }
  
  @Override
  public void visit(OperatorExpression e){
    Type deftype=create.class_type("Object");
    switch(e.getOperator()){
      case SubType:
        deftype=(Type)rewrite(e.getArg(1));
      case SuperType:
      {
        NameExpression n=(NameExpression)e.getArg(0);
        if (n.getName().equals("?")){
          wildcard_count++;
          String name="wildcard_"+wildcard_count;
          if (currentContractBuilder==null) Abort("no contract builder set");
          currentContractBuilder.given(create.field_decl(name, create.primitive_type(Sort.Class),deftype));
          currentContractBuilder.requires(create.expression(e.getOperator(),create.unresolved_name(name),rewrite(e.getArg(1))));
          result=create.unresolved_name(name);
          return;
        }
        break;
      }
    }
    super.visit(e);
    OperatorExpression res=(OperatorExpression) result;
    res.set_before(null);
    res.set_after(null);
    result=process_with_then(res,e);
  }
  
  @Override
  public void visit(LoopStatement s){
    super.visit(s);
    LoopStatement res=(LoopStatement)result;
    res.set_before(null);
    res.set_after(null);
    result=process_with_then(res,s);
  }
}
