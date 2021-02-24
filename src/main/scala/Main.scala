package com.github.kmn4.sst

import java.nio.file.{FileSystems, Files}

import com.typesafe.scalalogging.Logger

object Main extends App {
  val fname = args(0)
  val logger = Logger(s"bench.${fname.split('/').last.split('.').dropRight(1).mkString}")
  val path = FileSystems.getDefault().getPath(fname)
  val lexer = new smtlib.lexer.Lexer(new java.io.FileReader(path.toFile()))
  val parser = new smtlib.parser.Parser(lexer)
  val script = parser.parseScript
  // Ensure that alphabet includes at least 2 letters.
  new ParikhSolver(print = false, logger = logger, alphabet = "ab".toSet).executeScript(script)
}
