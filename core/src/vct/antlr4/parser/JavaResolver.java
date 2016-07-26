package vct.antlr4.parser;

import java.lang.reflect.Modifier;

import hre.HREError;
import hre.ast.MessageOrigin;
import vct.col.ast.*;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.Method.Kind;
import vct.col.ast.NameSpace.Import;
import vct.col.rewrite.AbstractRewriter;
import vct.util.ClassName;
import vct.util.Configuration;

public class JavaResolver extends AbstractRewriter {

  private ClassLoader path=this.getClass().getClassLoader();
  
  public JavaResolver(ProgramUnit source) {
    super(source);
  }
  
  private boolean ensures_loaded(String ... name){
    {
      ASTDeclaration decl=source().find_decl(name);
      if (decl!=null){
        if (decl instanceof ASTClass) return true;
        if (decl instanceof AxiomaticDataType) return true;
      }
    }
    if (name.length==1 && variables.containsKey(name[0])){
      return true;
    }
    if (target().find(name)!=null){
      return true;
    }
    try {
      ClassName cln=new ClassName(name);
      String cl_name=cln.toString();
      Class cl=path.loadClass(cl_name);
      System.err.printf("loading %s%n",cl_name);
      create.enter();
      create.setOrigin(new MessageOrigin("library class %s",cl_name));
      ASTClass res=create.new_class(name[name.length-1],null,null);
      target().library_add(cln,res);
      for(java.lang.reflect.Method m:cl.getMethods()){
        Class c=m.getReturnType();
        Type returns = convert_type(c);
        Class pars[]=m.getParameterTypes();
        DeclarationStatement args[]=new DeclarationStatement[pars.length];
        for(int i=0;i<pars.length;i++){
          args[i]=create.field_decl("x"+i, convert_type(pars[i]));
        }
        if (m.isVarArgs()){
          DeclarationStatement old=args[pars.length-1];
          args[pars.length-1]=create.field_decl(old.name,(Type)old.getType().getArg(0));
        }
        Method ast=create.method_kind(Method.Kind.Plain , returns, null, m.getName(),args, m.isVarArgs() , null);
        ast.setFlag(ASTFlags.STATIC,Modifier.isStatic(m.getModifiers()));
        res.add(ast);
      }
      for (java.lang.reflect.Constructor<?> m : cl.getConstructors()) {
    	  Class pars[]=m.getParameterTypes();
    	  DeclarationStatement args[]=new DeclarationStatement[pars.length];
    	  for(int i=0;i<pars.length;i++){
    		  args[i]=create.field_decl("x"+i, convert_type(pars[i]));
    	  }
    	  Method ast = create.method_kind(Kind.Constructor, null, null, m.getName(), args, null);
    	  res.add(ast);
      }
      for(java.lang.reflect.Field field:cl.getFields()){
        Class type=field.getType();
        DeclarationStatement decl=create.field_decl(field.getName(),convert_type(type));
        decl.setFlag(ASTFlags.STATIC,Modifier.isStatic(field.getModifiers()));
        res.add(decl);
      }
      create.leave();
      return true;
    } catch (ClassNotFoundException e) {
    }
    return false;
  }

  protected Type convert_type(Class c) {
    Type returns=null;
    if (c.isPrimitive()){
      switch(c.toString()){
      case "void":   
        returns=create.primitive_type(PrimitiveType.Sort.Void);
        break;
      case "boolean":   
        returns=create.primitive_type(PrimitiveType.Sort.Boolean);
        break;
      case "byte":   
        returns=create.primitive_type(PrimitiveType.Sort.Byte);
        break;
      case "char":   
        returns=create.primitive_type(PrimitiveType.Sort.Char);
        break;
      case "double":   
        returns=create.primitive_type(PrimitiveType.Sort.Double);
        break;
      case "float":   
        returns=create.primitive_type(PrimitiveType.Sort.Float);
        break;
      case "int":   
        returns=create.primitive_type(PrimitiveType.Sort.Integer);
        break;
      case "long":   
        returns=create.primitive_type(PrimitiveType.Sort.Long);
        break;
      case "short":   
        returns=create.primitive_type(PrimitiveType.Sort.Short);
        break;
      }
    } else if (c.isArray()) {
      returns=convert_type(c.getComponentType());
      returns=create.primitive_type(PrimitiveType.Sort.Array, returns);
    } else if (c.getName().equals("java.lang.String")){
      returns=create.primitive_type(PrimitiveType.Sort.String);
    } else {
      String name[]=c.getName().split("\\.");
      if (ensures_loaded(name)){
        returns=create.class_type(name);
      } else {
        Fail("could not load %s",c);
      }
    }
    if (returns==null){
      Fail("missing case (%s)",c);
    }
    return returns;
  }
  
  private String[] full_name(String ... name){
    if (ensures_loaded(name)){
      return name;
    }
    ClassName tmp;
    if (current_space!=null){
      tmp=new ClassName(name);
      tmp=tmp.prepend(current_space.getDeclName().name);
      if (ensures_loaded(tmp.name)){
        return tmp.name;
      }
      for(int i=current_space.imports.size()-1;i>=0;i--){
        Import imp=current_space.imports.get(i);
        if (imp.static_import) continue;
        if (imp.all){
          tmp=new ClassName(name);
          tmp=tmp.prepend(imp.name);
          if (ensures_loaded(tmp.name)){
            return tmp.name;
          }
        } else {
          String imp_name=imp.name[imp.name.length-1];
          if (name.length==1 && name[0].equals(imp_name)) {
            if (ensures_loaded(imp.name)){
              return imp.name;
            }            
          }
        }
      }
    }
    return null;
  }
  
  @Override
  public void visit(ClassType t){
    String name[]=t.getNameFull();
    if (ensures_loaded(name)){
      result=create.class_type(name,rewrite(t.getArgs()));
      return;
    }
    ClassName tmp;
    if (current_space!=null){
      tmp=new ClassName(name);
      tmp=tmp.prepend(current_space.getDeclName().name);
      if (ensures_loaded(tmp.name)){
        result=create.class_type(tmp.name,rewrite(t.getArgs()));
        return;
      }
      for(int i=current_space.imports.size()-1;i>=0;i--){
        Import imp=current_space.imports.get(i);
        if (imp.static_import) continue;
        if (imp.all){
          tmp=new ClassName(name);
          tmp=tmp.prepend(imp.name);
          if (ensures_loaded(tmp.name)){
            result=create.class_type(tmp.name,rewrite(t.getArgs()));
            return;
          }
        } else {
          String imp_name=imp.name[imp.name.length-1];
          if (name.length==1 && name[0].equals(imp_name)) {
            if (ensures_loaded(imp.name)){
              result=create.class_type(imp.name,rewrite(t.getArgs()));
              return;
            }            
          }
        }
      }
    }
    Fail("cannot resolve %s",new ClassName(name));
  }
  
  private NameSpace current_space=null;
  
  @Override
  public void visit(NameSpace ns){
    if (current_space!=null){
      throw new HREError("nested name spaces are future work");
    }
    current_space=ns;
    ns.imports.add(0,new NameSpace.Import(false,true,"java","lang"));
    ASTSequence seq=target();
    for(String part:ns.getDeclName().name){
      if (part==NameSpace.NONAME) continue;
      ASTClass cl=create.ast_class(part,ClassKind.Plain,null,null,null);
      cl.setFlag(ASTFlags.STATIC,true);
      seq.add(cl);
      seq=cl;
    }
    for(ASTNode item:ns){
      item=rewrite(item);
      item.setFlag(ASTFlags.STATIC,true);
      seq.add(item);
    }
    current_space=null;
    result=null;
  }

  @Override
  public void visit(NameExpression e){
    if (e.getKind()==NameExpression.Kind.Unresolved){
      String name=e.getName();
      VariableInfo info=variables.lookup(name);
      if (info!=null) {
        Debug("unresolved %s name %s found during standardize",info.kind,name);
        e.setKind(info.kind);
      } else {
        String cname[]=full_name(name);
        if (cname!=null){
          result=create.class_type(cname);
          return;
        }
      }
    }
    super.visit(e);
  }
  
}
