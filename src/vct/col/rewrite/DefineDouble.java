package vct.col.rewrite;


import hre.ast.MessageOrigin;
import hre.ast.Origin;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTNode;
import vct.col.ast.ClassType;
import vct.col.ast.DeclarationStatement;
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
    ASTClass Double=new ASTClass("Double",ClassKind.Abstract);
    Double.setOrigin(origin);
    ClassType type=create.class_type(double_name);
    DeclarationStatement binary[]=new DeclarationStatement[2];
    binary[0]=create.field_decl("x",type);
    binary[1]=create.field_decl("y",type);
    Double.add_dynamic(create.method_decl(type, null , "plus" , binary , null));
    Double.add_dynamic(create.method_decl(type, null , "mult" , binary , null));
    return Double;
  }
  
}
