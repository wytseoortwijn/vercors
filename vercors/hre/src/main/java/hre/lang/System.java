package hre.lang;

import java.io.*;
import java.lang.Thread.UncaughtExceptionHandler;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

/**
 * This class provides a way of providing feedback.
 */
public class System {
  public enum LogLevel {
    Silent(0, null),

    Abort(1, "ABRT"),     // Internal VerCors Error
    Result(2, "VERD"),    // The final verdict
    Warning(3, "WARN"),   // Warnings
    Info(4, "INFO"),      // User info
    Progress(5, "PROG"),  // Progress info
    Debug(6, "DEBG"),     // VerCors development info

    All(Integer.MAX_VALUE, "ALL ");

    private final int order;
    private final String shorthand;

    LogLevel(int order, String shorthand) {
      this.order = order;
      this.shorthand = shorthand;
    }

    public int getOrder() {
      return order;
    }

    public String getShorthand() {
      return shorthand;
    }
  }

  private static Map<Appendable, LogLevel> outputStreams = new HashMap<>();
  private static Map<Appendable, LogLevel> errorStreams = new HashMap<>();

  private static HashSet<String> debugFilterByClassName = new HashSet<>();
  private static HashSet<String> debugfilterByLine = new HashSet<>();

  private static HashSet<LogWriter> activeLogWriters = new HashSet<>();

  public static void setOutputStream(Appendable a, LogLevel level) {
    outputStreams.put(a, level);
  }

  public static void setErrorStream(Appendable a, LogLevel level) {
    errorStreams.put(a, level);
  }

  private static class LogWriter extends Writer {
      private String buffer = "";
      private LogLevel level;
      private Map<Appendable, LogLevel> outputs;

      LogWriter(LogLevel level, Map<Appendable, LogLevel> outputs) {
          this.level = level;
          this.outputs = outputs;
      }

      @Override
      public void write(char[] chars, int start, int end) throws IOException {
          buffer += new String(chars, start, end);
          writeLines();
      }

      private void writeLines() {
          String[] lines = buffer.split("\\r?\\n");

          for(int i = 0; i < lines.length - 1; i++) {
              System.log(level, outputs, "%s", lines[i]);
          }

          buffer = lines[lines.length - 1];
      }

      @Override
      public void flush() throws IOException {
          // Refuse, as flushing in this context may cause an additional unwanted newline.
      }

      @Override
      public void close() throws IOException {
          doFlush();
          activeLogWriters.remove(this);
      }

      private void doFlush() {
          if(!buffer.equals("")) {
              System.log(level, outputs, "%s", buffer);
              buffer = "";
          }
      }
  }

  private static PrintWriter getLogLevelWriter(LogLevel level, Map<Appendable, LogLevel> outputs) {
      LogWriter writer = new LogWriter(level, outputs);
      activeLogWriters.add(writer);
      return new PrintWriter(writer);
  }

  public static PrintWriter getLogLevelOutputWriter(LogLevel level) {
      return getLogLevelWriter(level, outputStreams);
  }

  public static PrintWriter getLogLevelErrorWriter(LogLevel level) {
      return getLogLevelWriter(level, errorStreams);
  }

  /**
   * Show debug messages from a particular class
   * @param className The name of the class to filter for
   */
  public static void addDebugFilterByClassName(String className) {
    debugFilterByClassName.add(className);
  }

  /**
   * Show debug messages from a particular line in a particular class
   * @param classLineCombo The class name and line number, in the format Class:no
   */
  public static void addDebugFilterByLine(String classLineCombo) {
    debugfilterByLine.add(classLineCombo);
  }

  private static void log(LogLevel level, Map<Appendable, LogLevel> outputs, String format, Object... args) {
    // Only format the string (expensive) when the message is actually outputted
    String message = null;

    for(LogWriter writer : activeLogWriters) {
        writer.doFlush();
    }

    for(Map.Entry<Appendable, LogLevel> entry : outputs.entrySet()) {
      if(entry.getValue().order >= level.getOrder()) {
        try {
          if(message == null) {
            message = "[" + level.getShorthand() + "] " + String.format(format + "%n", args);
          }

          entry.getKey().append(message);
        } catch(IOException e) {
          if(level != LogLevel.Abort) {
            Abort("IO Error: %s", e);
          }
        }
      }
    }
  }

  private static StackTraceElement getCallSite() {
    StackTraceElement[] stackTraceElements = Thread.currentThread().getStackTrace();

    int idx=2;
    while(stackTraceElements[idx].getClassName().equals("hre.lang.System")
        || stackTraceElements[idx].getClassName().equals("vct.col.ast.ASTFrame")) {
      idx++;
    }

    return stackTraceElements[idx];
  }
  
  /**
   * Emit an error message, print stack trace and abort.
   * 
   * This method is meant for internal errors which are fatal
   * and may be reported as bugs.
   * 
   * @param format The formatting of the message.
   * @param args The arguments to be formatted.
   */
  public static void Abort(String format, Object... args) {
    log(LogLevel.Abort, errorStreams, format, args);
    throw new HREExitException(1);
  }
  
  /**
   * Emit an error message and abort.
   * 
   * This function is meant to be used for external error conditions,
   * such as bad input.
   */
  public static void Fail(String format, Object... args) {
    Verdict(format, args);
    throw new HREExitException(1);
  }

  /**
   * Emit a verdict message, used only for the final verdict.
   */
  public static void Verdict(String format, Object... args) {
    StackTraceElement callSite = getCallSite();
    log(LogLevel.Debug, outputStreams, "At %s:%d:", callSite.getFileName(), callSite.getLineNumber());
    log(LogLevel.Result, outputStreams, format, args);
  }


  /**
   * Emit a debug message if the class calling this method is tagged for debugging.
   * 
   */
  public static void Debug(String format, Object... args) {
    StackTraceElement callSite = getCallSite();

    if(debugFilterByClassName.contains(callSite.getClassName())
          || debugfilterByLine.contains(callSite.getClassName() + ":" + callSite.getLineNumber())
    ) {
        log(LogLevel.Debug, errorStreams, "At %s:%d: ", callSite.getFileName(), callSite.getLineNumber());
        log(LogLevel.Debug, errorStreams, format, args);
    } else {
        log(LogLevel.All, errorStreams, "At %s:%d: ", callSite.getFileName(), callSite.getLineNumber());
        log(LogLevel.All, errorStreams, format, args);
    }
  }

  /**
   * Emit a stack trace as a debug message
   */
  public static void DebugException(Throwable e) {
    StringWriter sw = new StringWriter();
    e.printStackTrace(new PrintWriter(sw));
    for(String line : sw.toString().split("\\r?\\n")) {
      Debug("%s", line);
    }
  }

  /**
   * Emit a progress message.
   */
  public static void Progress(String format, Object... args) {
    log(LogLevel.Progress, outputStreams, format, args);
  }

  /**
   * Emit an output message.
   */
  public static void Output(String format, Object... args) {
    log(LogLevel.Info, outputStreams, format, args);
  }
  
  /**
   * Emit a warning message.
   */
  public static void Warning(String format, Object... args) {
    log(LogLevel.Warning, errorStreams, format, args);
  }

  public static Failure Failure(String format,Object...args) {
    StackTraceElement callSite = getCallSite();
    log(LogLevel.Debug, outputStreams, "At %s:%d:", callSite.getFileName(), callSite.getLineNumber());
    log(LogLevel.Result, outputStreams, format, args);
    return new Failure(String.format(format, args));
  }

  static {
    final UncaughtExceptionHandler parent=Thread.getDefaultUncaughtExceptionHandler();
    UncaughtExceptionHandler eh = new UncaughtExceptionHandler() {
      @Override
      public void uncaughtException(Thread t, Throwable e) {
        if (e instanceof HREExitException){
          java.lang.System.exit(((HREExitException) e).exit);
        }
        parent.uncaughtException(t,e);
      }
    };
    Thread.setDefaultUncaughtExceptionHandler(eh);
  }
}
