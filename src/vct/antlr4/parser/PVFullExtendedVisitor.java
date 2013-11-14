package vct.antlr4.parser;

import org.antlr.v4.runtime.tree.ParseTree;

import pv.parser.PVFullVisitor;

public interface PVFullExtendedVisitor<T> extends PVFullVisitor<T> {

  public void enter(ParseTree arg0);

  public void leave(ParseTree arg0);
  
  public void setMain(PVLWrappingVisitor<T> main);
}
