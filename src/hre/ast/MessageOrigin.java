// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package hre.ast;

import java.util.ArrayList;

/**
 * Origin that consists of a single text message.
 * @author sccblom
 *
 */
public class MessageOrigin implements Origin {

    private String message;
    public MessageOrigin(String format,Object ... args){
      this.message=String.format(format,args);
  }
    public MessageOrigin(String message){
      this.message=message;
  }
    public String toString(){
        return message;
    }
    @Override
    public void report(String level, Iterable<String> message) {
      System.out.println("=========================================");
      System.out.printf("%s in %s:",level,this.message);
      for(String line:message){
        System.out.printf("  %s%n",line);
      }
      System.out.println("=========================================");
    }

    @Override
    public void report(String level, String... message) {
      System.out.println("=========================================");
      System.out.printf("%s in %s:",level,this.message);
      for(String line:message){
        System.out.printf("  %s%n",line);
      }
      System.out.println("=========================================");
    }

}

