package vct.col.ast.stmt.decl;

import java.util.Arrays;
import java.util.Collections;

import scala.collection.Iterable;
import scala.collection.JavaConverters;
import vct.col.util.ASTMapping;
import vct.col.util.ASTMapping1;
import vct.col.ast.generic.ASTNode;
import vct.col.ast.stmt.decl.ASTDeclaration;
import vct.col.ast.util.ASTVisitor;
import vct.util.ClassName;

import static hre.lang.System.Debug;

public class ASTSpecial extends ASTDeclaration {

  public ASTNode getArg(int i){
    return args[i];
  }
  
  @Override
  public <R,A> R accept_simple(ASTMapping1<R,A> map, A arg){
    return map.map(this,arg);
  }

  @Override
  public Iterable<String> debugTreeChildrenFields() {
    return JavaConverters.iterableAsScalaIterable(Collections.singletonList("args"));
  }

  @Override
  public Iterable<String> debugTreePropertyFields() {
    return JavaConverters.iterableAsScalaIterable(Collections.singletonList("kind"));
  }

  public static enum Kind {
    Expression,
    With,
    Then,
    Proof,
    Import,
    Throw,
    Label,
    Exhale,
    Inhale,
    ActionHeader(4),
    CreateHistory(1),
    DestroyHistory(2),
    CreateFuture(2),
    DestroyFuture(1),
    SplitHistory(5),
    MergeHistory(5),
    ChooseHistory(4),
    /** Mark the subjects, whose invariants are available in an atomic region. */
    CSLSubject,
    Goto,
    SpecIgnoreStart,
    SpecIgnoreEnd,
    Wait,
    Notify,
    Fork,
    Join,
    Comment,
    Invariant,
    Contract, Requires, Ensures, Given(-1), Yields(-1), Modifies(-1), Pragma,
    RequiresAndEnsures(1),
    Accessible(-1),
    StaticEntry(0),
    InlineEntry(0),
    VolatileEntry(0),
    /** Lock statement. */
    Lock(1),
    /** Unfold statement. */
    Unlock(1),
    /** Open a predicate family. */
    Open(1),
    /** Close a predicate family. */
    Close(1),
    /** Fold statement. */
    Fold(1),
    /** Unfold statement. */
    Unfold(1),
    /**
     * Refute statement. Refute a fact at a point in the program.
     */
    Refute(1),
    /** Assert Statement. */
    Assert(-1),
    /** Assume statement. */
    Assume(1),
    /** Use statement for magic wand proofs */
    Use(1),
    /** QED statement for magic wand proofs */
    QED(1),
    /** Apply statement for magic wands */
    Apply(1),
    /** Declare a witness variable, for use in witness proofs. */
    Witness(1),
    /** Havoc statement. */
    Havoc(1),
    /** Hoare Predicate statement. This is the main ingredient of a Hoare Logic proof. */
    HoarePredicate(1),
    /**
     * Send permission statement for parallel loops.
     */
    Send(3),
    /**
     * Receive permission statement for parallel loops.
     */
    Recv(3),
    /**
     * Havoc a list of local variables.
     */
    Fresh(-1),
    /**
     * break a loop or switch.
     */
    Break(-1),
    /**
     * Continue a loop.
     */
    Continue(-1)
    ;

    
    
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
  
  public ASTSpecial(Kind kind,ASTNode ... args){
    super("<<special>>");
    if (kind == null) hre.lang.System.Abort("kind cannot be null");
    this.kind=kind;
    this.args=Arrays.copyOf(args,args.length);
  }

  
  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    try {
      visitor.visit(this);
    } catch (Throwable t){
      if (thrown.get()!=t){
        Debug("Triggered by %s:",getOrigin());
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
        Debug("Triggered by %s:",getOrigin());
        thrown.set(t);
      }
      throw t;
    }
  }
 
  @Override
  public boolean isSpecial(Kind with) {
    return kind==with;
  }

  @Override
  public ClassName getDeclName() {
    // TODO Auto-generated method stub
    return null;
  }


}
