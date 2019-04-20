package vct.main;

import java.util.Arrays;

import static hre.lang.System.*;

public class TestRun {

  public static void main(String[] args) {
    setOutputStream(System.out, LogLevel.Info);
    setErrorStream(System.err, LogLevel.Info);

    ToolTest tt=new ToolTest();
    VCTResult res=tt.run(Arrays.copyOfRange(args, 1, args.length));
    Output("expected/actual outcomes: %s/%s%n",args[0],res.verdict);
    
    if (args[0].equals(res.verdict.toString())){
      System.exit(0);
    } else {
      System.exit(1);
    }
  }

}
