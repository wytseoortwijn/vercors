package vct.util;

import hre.io.Container;
import hre.io.UnionContainer;
import hre.io.DirContainer;
import hre.io.JarContainer;
import hre.util.ContainerClassLoader;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Properties;



import static hre.System.*;

import vct.col.ast.ASTNode;
import vct.col.ast.CompilationUnit;
import vct.col.ast.ProgramUnit;

public class Parser {
  public static CompilationUnit parse(String language,String file){
    switch(language){
    case "pvl":
    case "c":
    case "c11":
    case "cl":
      language="antlr4";
      break;
//    case "cl":
//      Warning("clang parser causes many crashes and will be replaced");
//      language="clang";
//      break;
    }
    return plugin_parse(language,file);
  }

  private static CompilationUnit plugin_parse(String language,String file){
    File home=new File(System.getenv("VCT_HOME"));
    //System.err.printf("home is %s%n",home);
    ClassLoader loader=null;
    try {
      ArrayList<Container> path=new ArrayList();
      File parser=new File(home,language+"-parser");
      File plugin=new File(home,"plugins");
      File f=new File(parser,"bin");
      if (f.exists() && f.isDirectory()){
    	 Debug("loading %s parser from %s",language,f);
    	 path.add(new DirContainer(f));
      } else {
    	f=new File(parser,"vct-parser.jar");
    	if (f.exists() && f.isFile()) {
       	   Debug("loading %s parser from %s",language,f);
       	   path.add(new JarContainer(f));
    	} else {
    		f=new File(plugin,language+"-parser.jar");
       		if (f.exists() && f.isFile()) {
       			Debug("loading %s parser from %s",language,f);
       			path.add(new JarContainer(f));
       		} else {
       			Fail("could not find parser for %s",language);
       		}
    	}
      }
      // Latest build of JNI library.
      f=new File(parser,"Release");
      if (f.exists() && f.isDirectory()){
       	path.add(new DirContainer(f));
      }
      // Existing build of JNI library for current architecture.
      f=new File(new File(plugin,System.getProperty("os.name")),System.getProperty("os.arch"));
      if (f.exists() && f.isDirectory()){
       	path.add(new DirContainer(f));
      }
      // Find out is there is a library folder.
      f=new File(parser,"lib");
      if (!f.exists() || !f.isDirectory()){
          f=new File(parser,"libs");
      }
      if (f.exists() && f.isDirectory()){
    	  // scan library folder for jar files.
          File libs[]=f.listFiles();
          for(int i=0;i<libs.length;i++){
        	if (libs[i].getName().endsWith(".jar")){
        		path.add(new JarContainer(libs[i]));
        	}
          }
      }
      if (path.size()==1){
          loader = new ContainerClassLoader(path.get(0));
      } else {
          loader = new ContainerClassLoader(new UnionContainer(path));
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
    CompilationUnit result=parser.parse(new File(file));
    if (result==null){
      Fail("parser returned null");
    }
    return result;
  }

}
