package hre.io;

import java.io.PrintStream;

public class ForbiddenPrintStream extends PrintStream {
  ForbiddenPrintStream(PrintStream oldStream) {
    super(new ForbiddenOutputStream(oldStream));
  }
}
