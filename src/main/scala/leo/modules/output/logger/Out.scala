package leo.modules.output.logger

import java.util.logging.Level

import leo.Configuration
import leo.modules.output.Output


object Out extends Logging {
  override protected val loggerName = "Console"
  override protected lazy val defaultLogLevel = {val v = Configuration.VERBOSITY; if(v == null) Level.WARNING else v} // TODO : Fixme, set level and initialization
  override protected val useParentLoggers = false

  import java.util.logging.{ConsoleHandler, LogRecord, Formatter}
  addLogHandler(
    new ConsoleHandler {
      setLevel(defaultLogLevel)
      setFormatter(new Formatter {
        def format(record: LogRecord) = {
          s"[${record.getLevel.getLocalizedName}] \t ${record.getMessage} \n"
        }
      })
    }
  )

  def output(msg: Output): Unit = { println(msg.output) }
  def output(msg: String): Unit = { println(msg) }

}
