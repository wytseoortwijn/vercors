package vct.main;

import hre.io.Container;
import hre.io.UnionContainer;
import hre.io.DirContainer;
import hre.io.JarContainer;
import hre.util.ContainerClassLoader;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import static hre.System.*;

import vct.col.ast.ASTNode;
import vct.col.ast.ProgramUnit;

public class Parser {

  public static ProgramUnit parse(String language,String file){
    String vct_home=System.getenv("VCT_HOME");
    //System.err.printf("home is %s%n",vct_home);
    File home=new File(System.getenv("VCT_HOME"));
    //System.err.printf("home is %s%n",home);
    ClassLoader loader=null;
    try {
      File f=new File(new File(home,language+"-parser"),"bin");
      if (f.exists() && f.isDirectory()){
        Warning("loading %s parser from %s",language,f);
        Container main=new DirContainer(f);
        f=new File(new File(home,language+"-parser"),"lib");
        if (!f.exists() || !f.isDirectory()){
          f=new File(new File(home,language+"-parser"),"libs");
        }
        if (f.exists() && f.isDirectory()){
          File libs[]=f.listFiles();
          Container path[]=new Container[libs.length+1];
          path[0]=main;
          for(int i=0;i<libs.length;i++){
            path[i+1]=new JarContainer(libs[i]);
          }
          loader = new ContainerClassLoader(new UnionContainer(path));
        } else {
          loader = new ContainerClassLoader(main);
        }        
      } else {
        f=new File(new File(home,language+"-parser"),"vct-parser.jar");
        if (!f.exists()){
          f=new File(new File(home,"plugins"),language+"-parser.jar");
        }
        if (!f.exists()){
          Fail("could not find parser for %s",language);
        }
        Warning("loading %s parser from %s",language,f);
        loader = new ContainerClassLoader(new JarContainer(f));
      }
    } catch (IOException e) {
      Fail("could not load parser for %s",language);
    }
    Class parser_class=null;
    try {
      parser_class = Class.forName("vct."+language+".parser.Parser", true, loader);
    } catch (ClassNotFoundException e) {
      Fail("jar did not contain parser");
    }
    vct.col.util.Parser parser=null;
    try {
      Object tmp = parser_class.newInstance();
      if (tmp==null){
        Fail("could not instantiate parser");
      }
      if (!(tmp instanceof vct.col.util.Parser)){
        Fail("jar did not contain parser of correct type");
      }
      parser=(vct.col.util.Parser)tmp;
    } catch (InstantiationException e) {
      e.printStackTrace();
      Fail("could not instantiate parser");
    } catch (IllegalAccessException e) {
      e.printStackTrace();
      Fail("could not instantiate parser");
    }
    ProgramUnit result=parser.parse(new File(file));
    if (result==null){
      Fail("parser returned null");
    }
    return result;
  }

}
