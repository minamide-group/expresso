package com.github.kmn4.expresso

import com.github.kmn4.expresso.solver.DelegateSolver._
import com.github.kmn4.expresso.strategy.{JSSST2021Strategy, PreImageStrategy}
import com.typesafe.scalalogging.Logger
import java.io.{FileReader, InputStreamReader, Reader}
import java.nio.file.FileSystems
import scala.util.control.Exception.allCatch

object Main extends App {

  def solveWithDelegate(d: Delegate): Unit = {
    val r =
      for (ts <- d.transpile(script);
           res <- d.solve(ts)) yield res
    r match {
      case Left(TranspileError(msg)) => System.err.println(s"Transpilation error: $msg")
      case Left(ExecutionError(msg)) => System.err.println(s"Execution error: $msg")
      case Left(_)                   => ??? // for match exhaustiveness
      case Right(Some(model)) =>
        println("sat")
        println(model)
      case Right(None) =>
        println("unsat")
    }
  }

  // main

  val opt = Opt.parseOpt(args)
  val logger = Logger(s"bench.${opt.inputName}")
  val lexer = new smtlib.lexer.Lexer(opt.input)
  val parser = new smtlib.parser.Parser(lexer)
  val script = parser.parseScript

  // alpahbet to be added
  val alphabet = ('a' to 'c').toSet
  //  val alphabet = ('!' to '~').toSet
  //  val alphabet = (0 to 127).toSet

  opt.strategy match {
    case "preimage" =>
      new Solver(new PreImageStrategy(logger), print = true, alphabet = alphabet).executeScript(script)
    case "jssst" =>
      new Solver(new JSSST2021Strategy(logger), print = true, alphabet = alphabet).executeScript(script)
    case "z3" =>
      solveWithDelegate(Z3Delegate)
    case "cvc5" =>
      solveWithDelegate(CVC5Delegate)
  }
}

case class Opt(
    input: Reader = new InputStreamReader(System.in),
    inputName: String = "stdin",
    strategy: String = "jssst"
)
object Opt {
  def error(e: Throwable): Nothing = {
    System.err.println(s"Invalid argument: ${e.getMessage}")
    System.err.println(s"Usage: expresso [-in file] [-s ${knownStrategy mkString "|"}]")
    sys.exit(1)
  }
  def knownStrategy = Set("jssst", "preimage", "z3", "cvc5")
  def parseOpt(args: Array[String]): Opt = {
    val buf = args.toBuffer
    def withKey(key: String)(take: Int)(run: Int => Unit): Unit =
      buf.indexOf(key) match {
        case i if i >= 0 => run(i); buf.remove(i, take + 1)
        case _           => ()
      }
    var opt = Opt()
    allCatch.withApply(error).apply {
      withKey("-in")(1) { i =>
        val f = FileSystems.getDefault().getPath(buf(i + 1)).toFile()
        opt = opt.copy(input = new FileReader(f), inputName = f.getName.split('.').dropRight(1).mkString)
      }
      withKey("-s")(1) { i =>
        val s = knownStrategy
          .find(_ == buf(i + 1))
          .getOrElse { throw new Exception(s"unknown strategy ${buf(i + 1)}") }
        opt = opt.copy(strategy = s)
      }
      if (buf.nonEmpty) throw new Exception(s"unknown option ${buf.mkString(",")}")
      opt
    }
  }
}
