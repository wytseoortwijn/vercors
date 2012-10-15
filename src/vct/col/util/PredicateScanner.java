package vct.col.util;

import java.util.Set;

import vct.col.ast.ASTClass;
import vct.col.ast.AbstractScanner;
import vct.col.ast.Method;
import vct.util.ClassName;

public class PredicateScanner extends AbstractScanner {

  private Set<ClassName> predicates;
  
  public PredicateScanner(Set<ClassName> predicates) {
    this.predicates=predicates;
  }

  public void visit(Method m){
    if (m.kind==Method.Kind.Predicate){
      ASTClass cl=(ASTClass)m.getParent();
      ClassName name=new ClassName(cl.getFullName(),m.getName());
      predicates.add(name);
    }
  }

}
