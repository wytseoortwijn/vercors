// -*- tab-width:2 ; indent-tabs-mode:nil -*-

package vct.main;

import hre.ast.MessageOrigin;
import hre.debug.HeapDump;
import hre.io.PrefixPrintStream;
import hre.util.TestReport;

import java.io.*;

import vct.col.ast.*;
import vct.col.rewrite.AssignmentRewriter;
import vct.col.rewrite.GuardedCallExpander;
import vct.col.rewrite.JavaDefaultsRewriter;
import vct.col.rewrite.ResolveAndMerge;
import vct.col.rewrite.ReferenceEncoding;
import vct.col.util.SimpleTypeCheck;
import vct.col.util.XMLDump;
import vct.options.VerCorsToolOptionStore;
import vct.options.VerCorsToolSettings;
import static hre.System.*;

class Main
{
  private static ASTClass program;
  static {
    program=new ASTClass();
    program.setOrigin(new MessageOrigin("root class"));
  }
  
  private static void parseFile(String name){
    int dot=name.lastIndexOf('.');
    if (dot<0) {
      Fail("cannot deduce language of %s",name);
    }
    String lang=name.substring(dot+1);
    System.err.printf("Parsing %s file %s%n",lang,name);
    program.add_static(Parser.parse(lang,name));
    System.err.printf("Read %s succesfully\n",name);
  }

  private static int parseFilesFromFileList(String fileName)
  {
      LineNumberReader str = null;
      int cnt = 0;
      try
      {
         str = new LineNumberReader(new FileReader(new File(fileName)));
         String s;

         while ((s = str.readLine()) != null) {
          cnt++;
          parseFile(s);
         }
      }
      catch(Exception e) { e.printStackTrace(); }
      finally { if (str != null) try { str.close(); } catch(Exception e) {}  }
      return cnt;
   }

  public static void main(String[] args) throws Throwable
  {
    PrefixPrintStream out=new PrefixPrintStream(System.out);
    VerCorsToolSettings.parse(args);
    VerCorsToolOptionStore options = VerCorsToolSettings.getOptionStore();
    System.err.println("parsing inputs...");
    int cnt = 0;
    long l = System.currentTimeMillis();
    for(File f : options.getFiles()){
      parseFile(f.getPath());
      cnt++;
    }
    System.err.println("Parsed " + cnt + " files in: " + (System.currentTimeMillis() - l)+"ms");
    if (options.isPassesSet()){
      System.err.println("Rewriting AST");
      for(String pass:options.getPasses()){
        System.err.printf("Applying %s%n", pass);
        l = System.currentTimeMillis();
        if (pass.equals("exit")) {
          System.exit(0);
        } else if(pass.equals("dump")){
          HeapDump.tree_dump(out,program,ASTNode.class);
        } else if (pass.equals("check")){
          SimpleTypeCheck check=new SimpleTypeCheck(program);
          check.check(program);
        } else if(pass.equals("resolv")){
          program=(ASTClass)program.apply(new ResolveAndMerge());
        } else if(pass.equals("assign")){
          program=(ASTClass)program.apply(new AssignmentRewriter());
        } else if(pass.equals("jdefaults")){
          program=(ASTClass)program.apply(new JavaDefaultsRewriter());
        } else if(pass.equals("refenc")){
          program=(ASTClass)program.apply(new ReferenceEncoding());
        } else if(pass.equals("expand")){
          program=(ASTClass)program.apply(new GuardedCallExpander());
        } else {
          System.err.println("unknown pass "+pass);
          System.exit(1);
        }
        System.err.println("pass took " + (System.currentTimeMillis() - l)+"ms");
      }
    }
    System.out.printf("Chalice tool is %s%n",options.getRawChaliceTool() );
    System.out.printf("Boogie tool is %s%n",options.getRawBoogieTool() );
    if (options.isJavaSet()){
      vct.java.printer.JavaPrinter.dump(System.out,program);
    } else {
      TestReport res=null;
      if (options.isChaliceSet()){
        vct.boogie.Main.TestChalice(program,true,options.getRawChaliceTool());
      } else if (options.isBoogieSet()){
        res=vct.boogie.Main.TestBoogie(program);
      } else if (options.isBoogieFOLSet()){
        BoogieFOL.main(program);
      } else if (options.isZ3FOLSet()){
        Z3FOL.test();
      }
      if (res!=null) {
        System.out.printf("The overall verdict is %s%n",res.getVerdict());
      } else {
        System.out.printf("No overall verdict has been set. Check the output carefully!%n");
      }
    }
  }
}


