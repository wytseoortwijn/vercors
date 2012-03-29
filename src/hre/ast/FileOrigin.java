// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package hre.ast;

/**
 * Origin that denotes a range of characters in a File.
 * @author sccblom
 *
 */
public class FileOrigin implements Origin {

    private String file_name;
    private int first_line, first_col, last_line, last_col;
    public FileOrigin(String file_name,int first_line, int first_col, int last_line, int last_col){
        this.file_name=file_name;
        this.first_line=first_line;
        this.first_col=first_col;
        this.last_line=last_line;
        this.last_col=last_col;
        if (file_name==null) throw new Error("null file name");
    }
    
    public String toString(){
      if (last_line>=0) {
        return String.format(
            "file %s from line %d column %d until line %d column %d",
            file_name,first_line, first_col, last_line, last_col
        );
      } else {
        return String.format(
            "file %s at line %d column %d",
            file_name,first_line, first_col
        );       
      }
     
    }

    public FileOrigin merge(FileOrigin origin){
      return new FileOrigin(file_name,first_line,first_col,origin.last_line,origin.last_col);
    }

    public FileOrigin(String file_name,int first_line, int first_col){
      this.file_name=file_name;
      this.first_line=first_line;
      this.first_col=first_col;
      this.last_line=-1;
      this.last_col=-1;
      if (file_name==null) throw new Error("null file name");      
    }
}

