package vct.col.ast;

import java.util.Arrays;

import vct.util.ClassName;

public class ASTSpecialDeclaration extends ASTDeclaration {

  @Override
  public <R,A> R accept_simple(ASTMapping1<R,A> map,A arg){
    return map.map(this,arg);
  }

  public static enum Kind {
    Comment,
    Invariant,
    Contract, Requires, Ensures, Given, Yields, Modifies, Pragma, With, Then,
    Accessible;
    
    private final int arity;
    
    Kind(){
      this.arity=1;
    }
    Kind(int arity){
      this.arity=arity;
    }
    
    public int arity(){ return arity; }

  };

  public final Kind kind;
  
  public final ASTNode[] args;
  
  public ASTSpecialDeclaration(Kind kind,ASTNode ... args){
    super("<<special>>");
    this.kind=kind;
    this.args=Arrays.copyOf(args,args.length);
  }

  
  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    try {
      visitor.visit(this);
    } catch (Throwable t){
      if (thrown.get()!=t){
        System.err.printf("Triggered by %s:%n",getOrigin());
        thrown.set(t);
      }
      throw t;
    }
  }
  
  @Override
  public <T> T accept_simple(ASTMapping<T> map){
    try {
      return map.map(this);
    } catch (Throwable t){
      if (thrown.get()!=t){
        System.err.printf("Triggered by %s:%n",getOrigin());
        thrown.set(t);
      }
      throw t;
    }
  }
 
  
  public boolean isSpecial(Kind with) {
    return kind==with;
  }


  @Override
  public ClassName getDeclName() {
    // TODO Auto-generated method stub
    return null;
  }

}
