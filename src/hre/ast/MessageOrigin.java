// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package hre.ast;


public class MessageOrigin implements Origin {

    private String message;
    public MessageOrigin(String message){
        this.message=message;
    }
    public String toString(){
        return message;
    }

}

