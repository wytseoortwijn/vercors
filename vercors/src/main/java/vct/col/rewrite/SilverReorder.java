package vct.col.rewrite;

import java.util.Iterator;

import hre.util.MultiNameSpace;
import vct.col.ast.*;

public class SilverReorder extends AbstractRewriter {

  public SilverReorder(ProgramUnit source) {
    super(source);
  }
  
  private int count=0;
  
  MultiNameSpace <String,String> locals=new MultiNameSpace<String, String>();

  private BlockStatement main_block=null;
  
  @Override
  public void visit(IfStatement s){
    Debug("rewriting if");
    BlockStatement tmp=main_block;
    if(tmp==null){
      main_block=currentBlock;
    }
    super.visit(s);
    main_block=tmp;
  }
  
  
  @Override
  public void visit(NameExpression n){
    switch(n.getKind()){
    case Local:{
      Debug("lookup %s",n.getName());
      Iterator<String> names=locals.lookup(n.getName());
      if (!names.hasNext()){
        Debug("not found");
        result=create.local_name(n.getName());
      } else {
        String res=names.next();
        Debug("found %s",res);
        result=create.local_name(res);
      }
      break;    
    }
    case Label:{
      Debug("lookup %s",n.getName());
      Iterator<String> names=locals.lookup(n.getName());
      if (!names.hasNext()){
        Debug("not found");
        result=create.label(n.getName());
      } else {
        String res=names.next();
        Debug("found %s",res);
        Warning("mapping label %s to local",n.getName());
        result=create.local_name(res);
      }
      break;    
    }
    case Unresolved:{
      Debug("lookup %s",n.getName());
      Iterator<String> names=locals.lookup(n.getName());
      if (!names.hasNext()){
        Debug("not found");
        result=create.unresolved_name(n.getName());
      } else {
        String res=names.next();
        Debug("found %s",res);
        result=create.unresolved_name(res);
      }
      break;    
    }
    default:
      super.visit(n);
      break;
    }
  }
  
  @Override
  public void visit(DeclarationStatement d){
    if (currentBlock!=null){
      String name = d.name();
      count++;
      DeclarationStatement res=create.field_decl(
          name+"__"+count,
          rewrite(d.getType()),
          rewrite(d.initJava()));
      Debug("mapping %s",name);
      locals.add(name,name+"__"+count);
      if (main_block!=null){
        Debug("moving decl %s", d.name());
        main_block.prepend(res);
        result=null;
      } else {
        result=res;
      }
    } else {
      super.visit(d);
    }
  }
  
  @Override
  public void visit(BindingExpression e){
    BlockStatement tmp=main_block;
    main_block=null;
    super.visit(e);
    main_block=tmp;
  }
  
  @Override
  public void visit(LoopStatement s){
    locals.enter();

    BlockStatement tmp=main_block;
    if(tmp==null){
      main_block=currentBlock;
    }

    LoopStatement res=new LoopStatement();
    ASTNode child;
    child=s.getInitBlock();
    if (child!=null) {
      // The init block must be moved outside the loop statement and should not open a new scope, so declarations are
      // valid for the whole LoopStatement. Therefor, we rewrite it explicitly here.

      BlockStatement initBlock = (BlockStatement) child;
      BlockStatement newInitBlock = new BlockStatement();
      newInitBlock.setOrigin(initBlock.getOrigin());

      for(int i = 0; i < initBlock.getLength(); i++) {
        newInitBlock.addStatement(rewrite(initBlock.get(i)));
      }

      currentBlock.addStatement(newInitBlock);
    }
    child=s.getUpdateBlock();
    if (child!=null) res.setUpdateBlock(child.apply(this));
    child=s.getEntryGuard();
    if (child!=null) res.setEntryGuard(child.apply(this));
    child=s.getExitGuard();
    if (child!=null) res.setExitGuard(child.apply(this));
    res.appendContract(rewrite(s.getContract()));
    child=s.getBody();
    res.setBody(child.apply(this));
    res.set_before(rewrite(s.get_before()));
    res.set_after(rewrite(s.get_after()));
    res.setOrigin(s.getOrigin());
    result=res;

    main_block=tmp;    
    locals.leave();
  }
  
  @Override
  public void visit(Method m){
    locals.enter();
    super.visit(m);
    locals.leave();
  }

  public void visit(BlockStatement block){
    locals.enter();
    BlockStatement tmp=main_block;
    if(tmp==null){
      main_block=currentBlock;
    }
    super.visit(block);
    main_block=tmp;
    locals.leave();
  }
  
}
