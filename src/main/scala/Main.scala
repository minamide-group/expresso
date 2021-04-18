package com.github.kmn4.expresso

import com.github.kmn4.expresso.strategy.PreImageStrategy

import java.nio.file.{FileSystems, Files}
import com.typesafe.scalalogging.Logger
import com.github.kmn4.expresso.strategy.ThesisStrategy

// command line arguments:
// - 0 : constraint file name (.smt2 file)
// - 1 : solving strategy, either 'preimage' or 'thesis' (defaults to 'preimage')
object Main extends App {
  val fname = args(0)
  val logger = Logger(s"bench.${fname.split('/').last.split('.').dropRight(1).mkString}")
  val path = FileSystems.getDefault().getPath(fname)
  val lexer = new smtlib.lexer.Lexer(new java.io.FileReader(path.toFile()))
  val parser = new smtlib.parser.Parser(lexer)
  val script = parser.parseScript
  val checker = args.applyOrElse(1, (_: Int) => "preimage") match {
    case "preimage" => new PreImageStrategy(logger)
    case "thesis"   => new ThesisStrategy(logger)
    case s          => throw new Exception(s"Invalid strategy: ${s}\nPossible values are: preimage, thesis")
  }

  new Solver(
    checker = checker,
    print = true,
    logger = logger,
    alphabet = "ab".toSet // Ensure that alphabet includes at least 2 letters.
  ).executeScript(script)
}
