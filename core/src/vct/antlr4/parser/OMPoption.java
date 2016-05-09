package vct.antlr4.parser;

public class OMPoption implements OMPelement {

  public enum Kind { Private, NoWait }
  
  public final Kind kind;
  
  public OMPoption(Kind kind){
    this.kind=kind;
  }

}
