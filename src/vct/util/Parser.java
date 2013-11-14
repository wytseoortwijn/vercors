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
    case "c":
    case "c11":
    case "cl":
    case "java":
    case "pvl":
      return new vct.antlr4.parser.Parser().parse(new File(file));
    }
    Fail("no parser for %s is known");
    return null;
  }

}
