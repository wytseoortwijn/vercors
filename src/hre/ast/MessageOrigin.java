// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package hre.ast;

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

}

