package vct.col.rewrite;

import java.util.HashSet;

import vct.col.ast.*;


/**
 * This class strips unused extern functions from C programs.
 * It assumes that the C program is contained in the class Ref.
 * Note that it should be called after removing the spec-ignored parts.
 * 
 * @author Stefan Blom
 *
 */
public class StripUnusedExtern extends AbstractRewriter {

  public StripUnusedExtern(ProgramUnit source) {
    super(source);
  }
  
  private static HashSet<String> names=new HashSet();
  
  private class Scanner extends RecursiveVisitor<Object> {

    public Scanner(ProgramUnit source) {
      super(source);
    }
    
    @Override
    public void visit(Method m){
      if (names.contains(m.name)) return;
      names.add(m.name);
      super.visit(m);
    }
    
    @Override
    public void visit(MethodInvokation s){
      super.visit(s);
      if (s.getDefinition()==null){
        Warning("definition of call to %s not set, skipping scan",s.method);
      } else {
        s.getDefinition().apply(this);
      }
    }
    
  }

  private Scanner scanner=new Scanner(source());
  
  
  @Override
  public void visit(Method m){
    if (names.contains(m.name)){
      super.visit(m);
    }
  }
  @Override
  public ProgramUnit rewriteAll() {
    if (source().find("Ref")==null){
      return source();
    }
    int extern_count=0;
    for(Method m:source().find("Ref").methods()){
      if (m.isValidFlag(ASTFlags.EXTERN)){
        System.err.printf("skipping extern %s%n",m.name);
      } else {
        System.err.printf("scanning %s%n",m.name);
        if (!names.contains(m.name)){
          m.accept(scanner);
        }
      }
    }
    return super.rewriteAll();
  }


}
