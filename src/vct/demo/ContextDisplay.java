package vct.demo;

import hre.ast.Context;
import hre.ast.FileContext;
import hre.ast.FileOrigin;

public class ContextDisplay {

  public static void main(String args[]){
    Context c=new Context();
    c.add(args[0]);
    int begin=Integer.parseInt(args[1]);
    int end=Integer.parseInt(args[2]);
    FileOrigin o=new FileOrigin(args[0],begin,1,end,1);
    System.out.printf("origin %s is%n",o);
    c.printContext(System.out,o,2);
  }
}
