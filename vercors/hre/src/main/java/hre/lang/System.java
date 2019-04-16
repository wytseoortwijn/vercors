package hre.lang;

import hre.io.MessageStream;

import java.io.IOException;
import java.io.PrintStream;
import java.lang.Thread.UncaughtExceptionHandler;
import java.util.HashMap;
import java.util.Map;

/**
 * This class provides a way of providing feedback.
 */
public class System {
  public enum LogLevel {
    Quiet(0, null),

    Abort(1, "FATAL"),
    Result(2, "VERDICT"),
    Warning(3, "WARN"),
    Info(4, "INFO"),
    Progress(5, "PROGRESS"),
    Debug(6, "DEBUG"),

    All(Integer.MAX_VALUE, null);

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

  public static void setOutputStream(Appendable a, LogLevel level) {
    outputStreams.put(a, level);
  }

  public static void setErrorStream(Appendable a, LogLevel level) {
    errorStreams.put(a, level);
  }

  private static void log(LogLevel level, Map<Appendable, LogLevel> outputs, String format, Object... args) {
    String message = "[" + level.getShorthand() + "] " + String.format(format + "%n", args);

    for(Map.Entry<Appendable, LogLevel> entry : outputs.entrySet()) {
      if(entry.getValue().order >= level.getOrder()) {
        try {
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
    while(stackTraceElements[idx].getClassName().equals("hre.lang.System")){
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
    log(LogLevel.Debug, errorStreams, "At %s:%d:", callSite.getFileName(), callSite.getLineNumber());
    log(LogLevel.Debug, errorStreams, format, args);
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
    log(LogLevel.Warning, outputStreams, format, args);
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
