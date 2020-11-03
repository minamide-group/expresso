package com.github.kmn4.sst

import java.nio.file.{FileSystems, Files}

object Main extends App {
  val fname = args(0)
  val path = FileSystems.getDefault().getPath(fname)
  val lexer = new smtlib.lexer.Lexer(new java.io.FileReader(path.toFile()))
  val parser = new smtlib.parser.Parser(lexer)
  val script = parser.parseScript
  new Solver(()).executeTransPrint(script)
}
