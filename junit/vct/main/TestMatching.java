package vct.main;

import hre.ast.MessageOrigin;

import org.junit.Test;

import vct.col.ast.ASTNode;
import vct.col.ast.Hole;
import vct.col.ast.StandardOperator;
import vct.col.util.ASTFactory;

import junit.framework.TestCase;

public class TestMatching extends TestCase {

  
  @Test
  public void test(){
    ASTFactory create=new ASTFactory();
    create.setOrigin(new MessageOrigin(this.getClass().toString()));
    Hole x=new Hole();
    ASTNode pattern=create.expression(StandardOperator.Plus,x,create.constant(1));
    
    ASTNode term=create.expression(StandardOperator.Plus,create.unresolved_name("y"),create.constant(1));
    
    boolean res=pattern.match(term);
    if (res){
      System.out.printf("%s: ",res);
      vct.util.Configuration.getDiagSyntax().print(System.out,x.get());
    } else {
      fail("should not have matched");
    }
    
    term=create.expression(StandardOperator.Plus,create.unresolved_name("y"),create.constant(2));
    res=pattern.match(term);
    if (!res){
      System.out.printf("%s%n",res);
    } else {
      fail("should not have matched");
    }
    
  }
}
