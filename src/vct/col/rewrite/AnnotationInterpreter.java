package vct.col.rewrite;

import java.util.ArrayList;

import vct.col.ast.ASTFlags;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTReserved;
import vct.col.ast.ASTSpecial;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.ProgramUnit;
import vct.col.ast.Type;

public class AnnotationInterpreter extends AbstractRewriter {

  public AnnotationInterpreter(ProgramUnit source) {
    super(source);
  }

  @Override
  public void visit(Method m){
    Method.Kind kind=m.kind;
    ArrayList<ASTNode> ann=new ArrayList();
    Type returns=rewrite(m.getReturnType());
    ContractBuilder cb=new ContractBuilder();
    rewrite(m.getContract(),cb);
    String name=m.getName();
    DeclarationStatement args[]=rewrite(m.getArgs());
    ASTNode body=rewrite(m.getBody());
    boolean varArgs=m.usesVarArgs();
    if (m.annotated()) for(ASTNode a:m.annotations()){
      if (a==null){
        Warning("ignoring null annotation");
        continue;
      }
      if (a.isReserved(ASTReserved.Pure)){
        Warning("found pure annotation");
        kind=Method.Kind.Pure;
      } else if (a instanceof ASTSpecial) {
        ASTSpecial s=(ASTSpecial)a;
        if (s.kind==ASTSpecial.Kind.Comment && s.args[0].toString().equals("/*pure*/")) {
          Warning("found pure annotation");
          kind=Method.Kind.Pure; 
        } else {
          ann.add(rewrite(a));
        }
      } else {
        ann.add(rewrite(a));
      }
    }
    Method res=create.method_kind(kind, returns, cb.getContract(), name, args, varArgs, body);
    if (m.annotated()) {
      res.attach();
      for (ASTNode a : ann){
        if (a.isReserved(ASTReserved.Final)){
          res.setFlag(ASTFlags.FINAL, true);
        } else {
          res.attach(a);
        }
      }
    }
    result=res;
  }
}
