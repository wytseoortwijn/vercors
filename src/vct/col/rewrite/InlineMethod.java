package vct.col.rewrite;

import java.util.Hashtable;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import vct.col.ast.*;

public class InlineMethod extends Substitution {

  private String return_name;
  private String return_label;
  private String prefix;
  
  public InlineMethod(ProgramUnit source) {
    super(source, new Hashtable<NameExpression, ASTNode>());
  }

  private AtomicInteger count=new AtomicInteger();
  
  public void inline(BlockStatement block, String return_name, String return_label, Method m,ASTNode object, ASTNode[] args) {
    create.setOrigin(m.getOrigin());
    map.clear();
    map.put(create.reserved_name(ASTReserved.This),object);
    prefix="inline_"+count.incrementAndGet()+"_";
    DeclarationStatement decls[]=m.getArgs();
    for(int i=0;i<decls.length;i++){
      block.add(create.field_decl(prefix+decls[i].name, copy_rw.rewrite(decls[i].getType())));
      block.add(create.assignment(create.local_name(prefix+decls[i].name), copy_rw.rewrite(args[i])));
      map.put(create.local_name(decls[i].name),create.local_name(prefix+decls[i].name));
    }
    this.return_name=return_name;
    this.return_label=return_label;
    BlockStatement body=(BlockStatement)m.getBody();
    for(ASTNode s:body){
      block.add(rewrite(s));
    }
  }
  
  @Override
  public void visit(ReturnStatement r){
    if (r.getExpression()!=null){
      result=create.block(
          create.assignment(create.local_name(return_name),rewrite(r.getExpression())),
          create.special(ASTSpecial.Kind.Goto,create.label(return_label))
      );
    } else {
      result=create.special(ASTSpecial.Kind.Goto,create.label(return_label));
    }
  }

}
