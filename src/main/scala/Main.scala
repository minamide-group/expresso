package com.github.kmn4.sst

import java.nio.file.{FileSystems, Files}

object Main extends App {
  def parseAndSolve(input: String): Option[Map[String, String]] = {
    val forms = smtlib.Parser.parse(input).map(smtlib.Form.fromSExpr)
    val cstr = Constraint.SLConstraint.fromForms(forms)

    // Input / output alphabet is all characters that appears in given constraint + one additional char.
    val alphabet = {
      import Solver._
      val Constraint.SLConstraint(atoms, is, rs) = cstr
      val contained =
        (atoms.map(usedAlphabetAtomic) ++ rs.map(c => usedAlhpabetRegExp(c.re))).fold(Set.empty)(_ union _)
      val printable = ' ' to '~'
      printable.find(c => !contained.contains(c)) match {
        case None => contained
        case Some(c) => contained + c
      }
    }

    Solver
      .getModelIfSat(cstr, alphabet)
      .map(model => model.map { case (Constraint.StringVar(name), value) => name -> value.mkString })
  }
  val fname = args(0)
  val path = FileSystems.getDefault().getPath(".", fname)
  val input = Files.readAllBytes(path).map(_.toChar).mkString
  val output = parseAndSolve(input) match {
    case None => "unsat"
    case Some(model) =>
      val s = model.map { case (name, value) => s"""(define-const $name Int "${value}")""" }.mkString("\n  ")
      s"sat\n(model\n  $s\n)"
  }
  println(output)

}
