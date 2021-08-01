package com.github.kmn4.expresso

import com.github.kmn4.expresso.strategy.PreImageStrategy

import java.nio.file.FileSystems
import com.typesafe.scalalogging.Logger
import com.github.kmn4.expresso.strategy.JSSST2021Strategy

// command line arguments:
// - 0 : constraint file name (.smt2 file)
// - 1 : solving strategy, either 'preimage' or 'jssst' (defaults to 'jssst')
object Main extends App {
  val fname = args(0)
  val logger = Logger(s"bench.${fname.split('/').last.split('.').dropRight(1).mkString}")
  val path = FileSystems.getDefault().getPath(fname)
  val lexer = new smtlib.lexer.Lexer(new java.io.FileReader(path.toFile()))
  val parser = new smtlib.parser.Parser(lexer)
  val script = parser.parseScript
  val checker = args.applyOrElse(1, (_: Int) => "jssst") match {
    case "preimage" => new PreImageStrategy(logger)
    case "jssst"   => new JSSST2021Strategy(logger)
    case s          => throw new Exception(s"Invalid strategy: ${s}\nPossible values are: preimage, jssst")
  }

  // alpahbet to be added
  val alphabet = ('a' to 'c').toSet
//  val alphabet = ('!' to '~').toSet
//  val alphabet = (0 to 127).toSet

  new Solver(
    checker = checker,
    print = true,
    logger = logger,
    alphabet = alphabet
  ).executeScript(script)
}
