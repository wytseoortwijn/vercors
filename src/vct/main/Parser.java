package vct.main;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import static hre.System.*;

import vct.col.ast.ASTNode;

public class Parser {
  public static ASTNode parse(String language,String file){
    String vct_home=System.getenv("VCT_HOME");
    //System.err.printf("home is %s%n",vct_home);
    File home=new File(System.getenv("VCT_HOME"));
    //System.err.printf("home is %s%n",home);
    ClassLoader loader=null;
    try {
      File f=new File(new File(home,language+"-parser"),"vct-parser.jar");
      if (!f.exists()){
        f=new File(new File(home,"plugins"),language+"-parser.jar");
      }
      Warning("loading %s parser from %s",language,f);
      loader = new JarClassLoader(f);
    } catch (IOException e) {
      Fail("could not load parser for %s",language);
    }
    Class parser=null;
    try {
      parser = Class.forName("vct.parser.Parser", true, loader);
    } catch (ClassNotFoundException e) {
      Fail("jar did not contain parser");
    }
    Method main=null;
    try {
      main=parser.getMethod("parse",String.class);
    } catch (SecurityException e) {
      Fail("permission denied");
    } catch (NoSuchMethodException e) {
      Fail("method not found");
    }
    Object args[]=new Object[1];
    args[0]=file;
    Object result=null;
    try {
      result=main.invoke(null, args);
    } catch (IllegalArgumentException e) {
      Fail("IllegalArgumentException");
    } catch (IllegalAccessException e) {
      Fail("IllegalAccessException");
    } catch (InvocationTargetException e) {
      e.getCause().printStackTrace();
      Fail("parser throws exception: %s",e.getCause());
    }
    if (result==null){
      Fail("parser returned null");
    }
    if (!(result instanceof ASTNode)){
      Fail("parser result is not an AST");
    }
    return (ASTNode)result;
  }
}
