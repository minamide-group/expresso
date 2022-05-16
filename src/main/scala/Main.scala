package com.github.kmn4.expresso

import cats.data.Validated
import cats.data.ValidatedNel
import ch.qos.logback.{classic => logback}
import com.github.kmn4.expresso.strategy.JSSST2021Strategy
import com.github.kmn4.expresso.strategy.PreImageStrategy
import com.microsoft.z3.Version
import com.monovore.decline.CommandApp
import com.typesafe.scalalogging.Logger

import java.nio.file.FileSystems
import java.nio.file.Path

object Main
    extends CommandApp(
      name = "expresso",
      header = "Solve straight-line string constraints.",
      version = s"SNAPSHOT (with ${Version.getFullVersion()})",
      main = Options.opts map { arguments =>
        val path   = arguments.constraintFile
        val file   = path.toFile()
        val logger = Logger(s"bench.${file.getName().split('.').dropRight(1).mkString}")
        arguments.loggingLevel map Options.loggingLevels foreach
          logger.underlying.asInstanceOf[logback.Logger].setLevel
        val parser   = new smtlib.parser.Parser(new smtlib.lexer.Lexer(new java.io.FileReader(file)))
        val script   = parser.parseScript                 // might throw an exception
        val checker  = Options.strategies(arguments.strategyName)(logger)
        val alphabet = arguments.alphabet getOrElse Set() // alpahbet to be added

        logger.trace(s"checker=$checker")
        logger.trace(s"logger=$logger")
        logger.trace(s"alphabet=$alphabet")

        new Solver(
          checker = checker,
          print = true,
          logger = logger,
          alphabet = alphabet
        ).executeScript(script)
      }
    )

private final case class Arguments(
    constraintFile: Path,
    strategyName: String,
    alphabet: Option[Set[Char]],
    loggingLevel: Option[String],
)

private object Options {
  import com.monovore.decline._
  import cats.implicits._

  def opts: Opts[Arguments] = (constraintFile, strategy, alphabet, loggingLevel) mapN Arguments.apply

  val strategies = Map(
    "jssst"    -> (logger => new JSSST2021Strategy(logger)),
    "preimage" -> (logger => new PreImageStrategy(logger)),
  )

  val loggingLevels = scala.collection.immutable.SeqMap(
    "all"   -> logback.Level.TRACE,
    "trace" -> logback.Level.TRACE,
    "debug" -> logback.Level.DEBUG,
    "info"  -> logback.Level.INFO,
    "warn"  -> logback.Level.WARN,
    "error" -> logback.Level.ERROR,
    "off"   -> logback.Level.OFF,
  )

  val constraintFile = Opts
    .argument[Path](metavar = "constraint file")
    .validate("<constraint file> should exist")(_.toFile().exists())
  val strategy = Opts
    .argument[String]("strategy")
    .withDefault("jssst")
    .validate("<strategy> must be either \"preimage\" or \"jssst\"")(strategies.keySet.contains)
  val loggingLevel = {
    val keys   = loggingLevels.keys
    val msg    = s"one of ${keys.init.mkString(", ")}, or ${keys.last}"
    val keySet = keys.toSet
    Opts
      .option[String]("logging-level", help = msg)
      .validate(s"<logging-level> must be $msg")(keySet.contains)
      .orNone
  }
  val alphabet = Opts
    .option[Set[Char]](
      "alphabet",
      help = "alphabet to be considered additionally to those contained in a given constraint"
    )(new Argument[Set[Char]] {
      def read(string: String): ValidatedNel[String, Set[Char]] = string.split("-").toSeq match {
        case Seq(from, to) if from.length() == 1 && to.length() == 1 =>
          Validated.valid((from(0) to to(0)).toSet[Char])
        case _ => Validated.invalidNel("argument to --alphabet must be in the form <char>-<char>")
      }

      def defaultMetavar: String = "alphabet"
    })
    .orNone

}
