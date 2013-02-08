package vct.main;

import static hre.System.Warning;

import hre.ast.MessageOrigin;
import hre.ast.Origin;

import java.lang.reflect.Field;
import java.util.ArrayList;

import vct.col.ast.ASTClass;

import vct.col.ast.ASTNode;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.Contract;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.PrimitiveType;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.util.ASTFactory;
import vct.col.util.OriginFactory;
import vct.util.ClassName;
import clang.JCXCursor;
import clang.JCXIndex;
import clang.JCXTranslationUnit;
import clang.JCXCursorKind;
import clang.JCXType;
import clang.JCXTypeKind;

import static hre.System.Abort;

public class CLangParser implements JCXCursorKind,JCXTypeKind {

  private static class CursorOriginFactory implements OriginFactory<JCXCursor> {
    private MessageOrigin dummy=new MessageOrigin("dummy");
    @Override
    public Origin create(JCXCursor cursor) {
       //TODO: extract FileOrigin from cursor (extent).
       // see PrintCursorExtent procedure
       return dummy;
    }
    
  }
  
  private static ASTFactory<JCXCursor> create=new ASTFactory<JCXCursor>(new CursorOriginFactory());
  
  public static ProgramUnit parse(String file){
    String vct_home=System.getenv("VCT_HOME");
    //System.err.printf("home is %s%n",vct_home);
    String path=System.getProperty("java.library.path");
    path=((path==null)?"":path+":")+vct_home+"/clang-parser/jni/Release";
    System.setProperty("java.library.path", path);
    Warning("java.library.path=%s", path);
    Field fieldSysPath;
    try {
      fieldSysPath = ClassLoader.class.getDeclaredField( "sys_paths" );
      fieldSysPath.setAccessible( true );
      fieldSysPath.set( null, null );
    } catch (NoSuchFieldException | SecurityException | IllegalArgumentException | IllegalAccessException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    System.loadLibrary("CLangNative");
    JCXIndex idx=new JCXIndex(false,true);
    JCXTranslationUnit tu=new JCXTranslationUnit(idx,new String[]{file});
    JCXCursor cur=tu.getCursor();
    show("",cur);
    ProgramUnit pu=new ProgramUnit();
    pu.addClass(new ClassName(file),(ASTClass)convert(cur));
    return pu;
  }

  private static ASTNode convert(JCXCursor cur) {
    int kind=cur.getKind();
    JCXCursor children[]=cur.getChildren();
    String name=cur.getCursorSpelling();
    switch(kind){
      case CXCursor_TranslationUnit:{
        ASTClass cl=create.ast_class(cur, "<<main>>", ASTClass.ClassKind.Plain , new ClassType[0], new ClassType[0]);
        for(JCXCursor item : children){
          ASTNode tmp=convert(item);
          if (tmp!=null){
            cl.add_static(tmp);
          }
        }
        return cl;
      }
      case CXCursor_FunctionDecl:{
    	JCXType jcxtype=cur.getResultType();
    	Warning("return type %s",jcxtype.getSpelling());
        Type t=convert(cur,jcxtype);
        Contract contract=null;
        ArrayList<DeclarationStatement> params=new ArrayList<DeclarationStatement>();
        ASTNode body=null;
        for(JCXCursor item : children){
          switch(item.getKind()){
          case CXCursor_UnexposedAttr:
            Warning("skipping UnexposedAttr");
            continue;
          case CXCursor_ParmDecl:
            params.add((DeclarationStatement)convert(item));
            continue;
          case CXCursor_CompoundStmt:
            if (body!=null){
              Abort("function already has a body.");
            }
            body=convert(item);
            continue;
          default:
            Abort("unexpected cursor in function declaration: %d",item.getKind());
          }
        }
        DeclarationStatement args[]=params.toArray(new DeclarationStatement[0]);
        return create.method_decl(cur, t, contract, name, args, body);
      }
      case CXCursor_ParmDecl:{
    	JCXType jcxtype=cur.getType();
    	Warning("decl type: %s",jcxtype.getSpelling());
    	Type t=convert(cur,jcxtype);
    	return create.field_decl(cur, name , t);
      }
      case CXCursor_CompoundStmt:{
    	  BlockStatement block=create.block(cur);
    	  for(JCXCursor item:children){
    		  ASTNode tmp=convert(item);
    		  if (tmp!=null) block.add_statement(tmp);
    	  }
    	  return block;
      }
      case CXCursor_BinaryOperator:{
        if (children.length!=2){
          Abort("binary operator with %d children",children.length);
        }
        StandardOperator op=null;
        switch(cur.getCursorSpelling()){
          case "=":
            op=StandardOperator.Assign;
            break;
          case "+":
            op=StandardOperator.Plus;
            break;           
          default:
            Abort("unknown operator %s",cur.getCursorSpelling());
        }
        return create.expression(cur,op,convert(children));
      }
      case CXCursor_IntegerLiteral:{
        String val=cur.getCursorSpelling();
        Warning("integer: %s",val);
        return create.constant(cur,Integer.parseInt(val));
      }
      case CXCursor_UnexposedExpr:{
        //TODO: check and fix!
        return convert(children[0]);
      }
      case CXCursor_ReturnStmt:{
        return create.return_statement(cur,convert(children));
      }
      case CXCursor_CompoundAssignOperator:{
        Warning("assignment [%s/%s]",cur.getCursorSpelling(),cur.getDisplayName());
        return null;
      }
      case CXCursor_DeclRefExpr:{
        Warning("name %s",cur.getCursorSpelling());
        return create.unresolved_name(cur,cur.getCursorSpelling());
      }
      case CXCursor_DeclStmt:
      case CXCursor_TypedefDecl:
      
      case CXCursor_CallExpr:
          Warning("skipping cursor of kind %d",kind);
          return null;
    }
    Abort("unimplemented cursor kind %d",kind);
    return null;
  }

  private static ASTNode[] convert(JCXCursor[] children) {
    ASTNode result[]=new ASTNode[children.length];
    for(int i=0;i<children.length;i++){
      result[i]=convert(children[i]);
    }
    return result;
  }

  private static Type convert(JCXCursor cur,JCXType jcxtype) {
	    int kind=jcxtype.getKind();
	    String name=jcxtype.getSpelling();
	    switch(kind){
    	case CXType_Void:
    		return create.primitive_type(cur, PrimitiveType.Sort.Void);
    	case CXType_Int:
    		return create.primitive_type(cur, PrimitiveType.Sort.Integer);
      case CXType_Bool:
        return create.primitive_type(cur, PrimitiveType.Sort.Boolean);
      case CXType_Float:
        return create.primitive_type(cur, PrimitiveType.Sort.Float);
    	case CXType_Char_S:
    		return create.primitive_type(cur, PrimitiveType.Sort.Char);
    	case CXType_Pointer:
    		JCXType target=jcxtype.getPointeeType();
    		Warning("pointer to %s",target.getSpelling());
    		// TODO: return pointer instead of array type!
    		return create.primitive_type(cur, PrimitiveType.Sort.Array,convert(cur,target));
	    }
	    Abort("unimplemented type kind %d",kind);
	    return null;
  }

public static void show(String prefix,JCXCursor cur){
    System.out.printf("%s<%d>%n",prefix,cur.getKind());
    for(JCXCursor child : cur.getChildren()){
      show(prefix+"  ",child);
    }
    System.out.printf("%s</%d>%n",prefix,cur.getKind());
  }

}
