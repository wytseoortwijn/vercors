// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

public class BooleanValue implements Value {
  public final boolean value;
  public BooleanValue(boolean value){
    this.value=value;
  }
  public String toString(){
    return value?"true":"false";
  }
  public boolean equals(Object o){
    return o.equals(value);
  }
}


