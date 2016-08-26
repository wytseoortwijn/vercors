package vct.antlr4.parser;

public class OMPoption implements OMPelement {

  public enum Kind { Private, NoWait, Schedule }
  
  public enum Schedule { Static, Dynamic }
  
  public final Kind kind;
  
  public final Schedule schedule;
  
  public OMPoption(Kind kind){
    this.kind=kind;
    this.schedule=null;
  }
  
  public OMPoption(Kind kind,Schedule schedule){
    this.kind=kind;
    this.schedule=schedule;
  }

  public static boolean nowait(OMPoption[] options) {
    for(OMPoption o:options){
      if (o==null) continue;
      if (o.kind==Kind.NoWait){
        return true;
      }
    }
    return false;
  }

  public static boolean static_schedule(OMPoption[] options) {
    for(OMPoption o:options){
      if (o==null) continue;
      if (o.kind==Kind.Schedule){
        return o.schedule==Schedule.Static;
      }
    }
    return false;
  }

}
