package vct.antlr4.parser;

import static hre.System.Fail;

import java.util.BitSet;
import java.util.concurrent.atomic.AtomicInteger;

import org.antlr.v4.runtime.ANTLRErrorListener;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.atn.ATNConfigSet;
import org.antlr.v4.runtime.dfa.DFA;

public final class ErrorCounter implements ANTLRErrorListener {
  public  final AtomicInteger count =new AtomicInteger();

  public final String file_name;
  
  public ErrorCounter(String file_name){
    this.file_name=file_name;
  }
  private int ofs=0;
    
  public void set_ofs(int ofs){
    this.ofs=ofs;
  }

  @Override
  public void syntaxError(Recognizer<?, ?> arg0, Object arg1, int arg2,
      int arg3, String arg4, RecognitionException arg5) {
    // TODO Auto-generated method stub
    hre.System.Warning("line %d:%d %s%n",ofs+arg2,arg3,arg4);
    count.incrementAndGet();
  }

  @Override
  public void reportContextSensitivity(Parser arg0, DFA arg1, int arg2,
      int arg3, int arg4, ATNConfigSet arg5) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void reportAttemptingFullContext(Parser arg0, DFA arg1, int arg2,
      int arg3, BitSet arg4, ATNConfigSet arg5) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void reportAmbiguity(Parser arg0, DFA arg1, int arg2, int arg3,
      boolean arg4, BitSet arg5, ATNConfigSet arg6) {
    // TODO Auto-generated method stub
    
  }

  public void report() {
    if (count.get()>0){
      Fail("encountered %d syntax error(s) in %s",count.get(),file_name);
    }
  }
}