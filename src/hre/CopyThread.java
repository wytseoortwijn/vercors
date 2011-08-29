package hre;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

public class CopyThread extends Thread {

  private InputStream input;
  private boolean close_in=false;
  private OutputStream output;
  private boolean close_out=false;
  private IOException err=null;
  
  public CopyThread(File input, OutputStream output) throws FileNotFoundException {
    this.input=new FileInputStream(input);
    close_in=true;
    this.output=output;
    setDaemon(true);
  }
  public CopyThread(InputStream input, File output) throws FileNotFoundException {
    this.input=input;
    this.output=new FileOutputStream(output);
    close_out=true;
    setDaemon(true);
  }
  public CopyThread(InputStream input, OutputStream output) {
    this.input=input;
    this.output=output;
    setDaemon(true);
  }
  
  public void run(){
    while(err==null){
      try {
        int ch=input.read();
        if (ch<0) break;
        output.write(ch);
      } catch (IOException e){
        err=e;
      }
    }
    try {
      if (close_in) input.close();
    } catch (IOException e){
      if (err==null) err=e;
    }
    try {
      if (close_out) output.close();
    } catch (IOException e){
      if (err==null) err=e;
    }
  }

  public IOException getError(){
    return err;
  }
}
