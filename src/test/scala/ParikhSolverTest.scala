package com.github.kmn4.sst

import org.scalatest.funsuite._
import org.scalactic.source.Position

class ParikhSolverTest extends AnyFunSuite {
  def withScript[T](reader: java.io.Reader)(body: smtlib.trees.Commands.Script => T): T = {
    val lexer = new smtlib.lexer.Lexer(reader)
    val parser = new smtlib.parser.Parser(lexer)
    val script = parser.parseScript
    body(script)
  }
  def withExecuteScript[T](reader: java.io.Reader)(body: ParikhSolver => T): T = withScript(reader) {
    script =>
      val solver = new ParikhSolver(())
      solver.executeScript(script)
      body(solver)
  }
  def testWithInfoTime[T](testName: String, testTags: org.scalatest.Tag*)(
      testFun: => Any
  )(implicit pos: Position): Unit = test(testName, testTags: _*) {
    val started = System.nanoTime()
    testFun
    val finished = System.nanoTime()
    info(s"Took ${(finished - started) / 1000000} ms")
  }
  def testSAT(
      constraint: String
  )(assertions: (Map[String, String], Map[String, Int]) => Unit)(implicit pos: Position) =
    withExecuteScript(new java.io.StringReader(constraint)) { solver =>
      testWithInfoTime(s"test SAT\n${constraint.trim}") {
        solver.checker().models() match {
          case Some((sModel, iModel)) => assertions(sModel, iModel)
          case None                   => fail()
        }
      }
    }
  def testUNSAT(constraint: String)(implicit pos: Position) =
    withExecuteScript(new java.io.StringReader(constraint)) { solver =>
      testWithInfoTime(s"test UNSAT\n${constraint.trim}") {
        assert(solver.checker().models().isEmpty)
      }
    }

  testSAT("""
(declare-const x String)
(declare-const y String)

(assert (= y (str.replace_pcre_all x (str.to_pcre "aab") (pcre.replacement "b"))))
(assert (str.in.re y (re.++ re.all (str.to.re "aab") re.all)))
(check-sat)
(get-model)
""") { (sModel, iModel) =>
    val (x, y) = (sModel("x"), sModel("y"))
    assert(y == x.replaceAll("aab", "b"))
    assert(".*aab.*".r.matches(y))
    ()
  }

  testSAT("""
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.* (str.to.re "a"))))
(assert (= y (str.replace_pcre_all x (pcre.+ (str.to_pcre "b")) (pcre.replacement ""))))
(assert (str.in.re y (re.* (str.to.re "a"))))
(check-sat)
(get-model)
""") { (_, _) => () }

  testUNSAT(
    """
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.* (str.to.re "ab"))))
(assert (= y (str.replace_pcre x (pcre.+ (str.to_pcre "ab")) (pcre.replacement ""))))
(assert (str.in.re y (re.comp (str.to.re ""))))
(check-sat)
"""
  )

  testSAT(
    """
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.* (str.to.re "ab"))))
(assert (= y (str.replace_pcre x (str.to_pcre "ab") (pcre.replacement ""))))
(assert (str.in.re y (re.comp (str.to.re ""))))
(check-sat)
"""
  ) { (sm, im) =>
    val (x, y) = (sm("x"), sm("y"))
    assert("(ab)*".r.matches(x))
    assert(y == x.replaceFirst("ab", ""))
    assert(y != "")
  }

  testUNSAT("""
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.+ (str.to.re "ab"))))
(assert (= y (str.replace_pcre_all x (pcre.+ (str.to_pcre "ab")) (pcre.replacement "a"))))
(assert (str.in.re y (re.comp (str.to.re "a"))))
(check-sat)
""")

  implicit class AtMostSubstring(s: String) {
    def atmostSubstring(idx: Int, len: Int): String = {
      if (0 <= idx && idx < s.length && 0 < len) s.substring(idx, idx + math.min(len, s.length - idx))
      else ""
    }
  }

  testSAT("""
(declare-const x String)
(declare-const y String)
(declare-const i Int)

(assert (str.in.re x (re.+ (str.to.re "ab"))))
(assert (and (<= 0 i) (< i (str.len x))))
(assert (= y (str.substr x i 2)))
(assert (str.in.re y (re.comp (str.to.re "ab"))))
""") {
    case (sModel, iModel) =>
      val (x, y, i) = (sModel("x"), sModel("y"), iModel("i"))
      assert("(ab)+".r.matches(x))
      assert(0 <= i && i < x.length)
      assert(y == x.atmostSubstring(i, 2))
      assert(!"ab".r.matches(y))
  }
}