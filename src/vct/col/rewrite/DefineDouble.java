package vct.col.rewrite;


import hre.ast.MessageOrigin;
import hre.ast.Origin;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ClassType;
import vct.col.ast.Method;
import vct.col.util.ASTFactory;

public class DefineDouble {

  public static final String double_name[]={"Double"};
  
  public static ASTClass rewrite(ASTClass program){
    AbstractRewriter rw=new RewriteDoubleDefinition();
    program=(ASTClass)program.apply(rw);
    program.add_static(generate_double_spec());
    return program;
  }

  private static ASTNode generate_double_spec() {
    final ASTFactory create=new ASTFactory();
    Origin origin=new MessageOrigin("Generated during fake double pass");
    create.setOrigin(origin);
    ASTClass Double=new ASTClass("Double");
    Double.setOrigin(origin);
    ClassType type=create.class_type(double_name);
    Double.add_dynamic(create.method_decl(type, null , "add" , new ASTNode[0] , null));
    return Double;
  }
  
}
