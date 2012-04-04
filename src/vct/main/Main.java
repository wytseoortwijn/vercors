// -*- tab-width:2 ; indent-tabs-mode:nil -*-

package vct.main;

import hre.ast.MessageOrigin;
import hre.debug.HeapDump;
import hre.io.PrefixPrintStream;
import hre.util.TestReport;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

import vct.col.ast.*;
import vct.col.rewrite.AssignmentRewriter;
import vct.col.rewrite.DefineDouble;
import vct.col.rewrite.FinalizeArguments;
import vct.col.rewrite.Flatten;
import vct.col.rewrite.GlobalizeStatics;
import vct.col.rewrite.GuardedCallExpander;
import vct.col.rewrite.JavaDefaultsRewriter;
import vct.col.rewrite.ReorderAssignments;
import vct.col.rewrite.ResolveAndMerge;
import vct.col.rewrite.ReferenceEncoding;
import vct.col.rewrite.SimplifyCalls;
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
    if (lang.equals("pvl")){
      //TODO: fix this kludge.
      vct.col.ast.ASTNode.pvl_mode=true;
    }
    Progress("Parsing %s file %s",lang,name);
    program.add_static(Parser.parse(lang,name));
    Progress("Read %s succesfully",name);
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
    if(options.isDebugSet()){
      for(String name:options.getDebug()){
        hre.System.EnableDebug(name,java.lang.System.err,"vct("+name+")");
      }
    }
    hre.System.setProgressReporting(options.isProgressSet());
    
    Progress("parsing inputs...");
    int cnt = 0;
    long startTime = System.currentTimeMillis();
    for(File f : options.getFiles()){
      parseFile(f.getPath());
      cnt++;
    }
    Progress("Parsed %d files in: %dms",cnt,System.currentTimeMillis() - startTime);
    List<String> passes=null;
    if (options.isPassesSet()){
    	passes=options.getPasses();
    } else if (options.isBoogieSet()) {
    	passes=new ArrayList<String>();
      passes.add("resolv");
      passes.add("check");
      passes.add("flatten");
      passes.add("assign");
      passes.add("finalize_args");
      passes.add("reorder");
      passes.add("simplify_calls");
    	passes.add("boogie");
    } else if (options.isChaliceSet()) {
    	passes=new ArrayList<String>();
    	passes.add("jdefaults");
    	passes.add("resolv");
      passes.add("check");
      passes.add("flatten");
      passes.add("resolv");
      passes.add("check");
      passes.add("define_double");
      passes.add("resolv");
      passes.add("check");     
    	passes.add("assign");
      passes.add("reorder");
    	passes.add("expand");
    	passes.add("resolv");
    	passes.add("check");
    	passes.add("chalice");
    } else {
    	Abort("no back-end or passes specified");
    }
    {
      TestReport res=null;
      for(String pass:passes){
        if (res!=null){
          Progress("Ignoring intermediate verdict %s",res.getVerdict());
          res=null;
        }
        Progress("Applying %s ...", pass);
        startTime = System.currentTimeMillis();
        if (pass.equals("exit")) {
          System.exit(0);
        } else if(pass.equals("dump")){
          HeapDump.tree_dump(out,program,ASTNode.class);
        } else if (pass.equals("finalize_args")){
          program=(ASTClass)program.apply(new FinalizeArguments());
        } else if (pass.equals("check")){
          new SimpleTypeCheck(program).check(program);
        } else if(pass.equals("flatten")){
          program=(ASTClass)program.apply(new Flatten());
        } else if(pass.equals("globalize")){
          program=(ASTClass)program.apply(new GlobalizeStatics());
        } else if(pass.equals("resolv")){
          program=(ASTClass)program.apply(new ResolveAndMerge());
        } else if(pass.equals("reorder")){
          program=(ASTClass)program.apply(new ReorderAssignments());
        } else if(pass.equals("assign")){
          program=(ASTClass)program.apply(new AssignmentRewriter());
        } else if(pass.equals("jdefaults")){
          program=(ASTClass)program.apply(new JavaDefaultsRewriter());
        } else if(pass.equals("simplify_calls")){
          program=(ASTClass)program.apply(new SimplifyCalls());
        } else if(pass.equals("refenc")){
          program=(ASTClass)program.apply(new ReferenceEncoding());
        } else if(pass.equals("expand")){
          program=(ASTClass)program.apply(new GuardedCallExpander());
        } else if(pass.equals("boogie-fol")){
          Z3FOL.test();
          BoogieFOL.main(program);
        } else if(pass.equals("boogie")){
          res=vct.boogie.Main.TestBoogie(program);
        } else if(pass.equals("define_double")){
          program=DefineDouble.rewrite(program);
        } else if(pass.equals("chalice")){
          res=vct.boogie.Main.TestChalice(program);
        } else if(pass.equals("java")){
          vct.java.printer.JavaPrinter.dump(System.out,program);
        } else {
          Fail("unknown pass %s",pass);
        }
        Progress(" ... pass took %d ms",System.currentTimeMillis()-startTime);
      }
      if (res!=null) {
        Output("The final verdict is %s",res.getVerdict());
      } else {
        Fail("No overall verdict has been set. Check the output carefully!");
      }
    }
  }
}


