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
      val solver = new ParikhSolver(ParikhSolver.SolverOption(print = false))
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
    testWithInfoTime(s"test SAT\n${constraint.trim}") {
      withExecuteScript(new java.io.StringReader(constraint)) { solver =>
        solver.checker().models() match {
          case Some((sModel, iModel)) => assertions(sModel, iModel)
          case None                   => fail()
        }
      }
    }
  def testUNSAT(constraint: String)(implicit pos: Position) =
    testWithInfoTime(s"test UNSAT\n${constraint.trim}") {
      withExecuteScript(new java.io.StringReader(constraint)) { solver =>
        assert(solver.checker().models().isEmpty)
      }
    }

  def withFileReader[T](fname: String)(body: java.io.FileReader => T): T = {
    val path = java.nio.file.FileSystems.getDefault().getPath(fname)
    val reader = new java.io.FileReader(path.toFile())
    try {
      body(reader)
    } finally {
      reader.close()
    }
  }

  def filePath(name: String): String = s"constraints/bench/$name.smt2"

  def testFileSAT(
      name: String
  )(assertions: (Map[String, String], Map[String, Int]) => Unit)(implicit pos: Position) =
    testWithInfoTime(s"""test SAT: "$name"""") {
      withFileReader(filePath(name)) { reader =>
        withExecuteScript(reader) { solver =>
          solver.checker().models() match {
            case Some((sModel, iModel)) => assertions(sModel, iModel)
            case None                   => fail()
          }
        }
      }
    }
  def testFileUNSAT(name: String)(implicit pos: Position) =
    testWithInfoTime(s"""test UNSAT: "$name"""") {
      withFileReader(filePath(name)) { reader =>
        withExecuteScript(reader) { solver => assert(solver.checker().models().isEmpty) }
      }
    }

  testFileSAT("deleteall") { (_, _) => () }

  // Simple replace_pcre_all (match constant)
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

  // Delete all b+. Should be equivalent to (replace_all x "b" "")
  testSAT("""
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.* (str.to.re "a"))))
(assert (= y (str.replace_pcre_all x (pcre.+ (str.to_pcre "b")) (pcre.replacement ""))))
(assert (str.in.re y (re.* (str.to.re "a"))))
(check-sat)
(get-model)
""") { (_, _) => () }

  // Unsat case.
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

  // Ensure replace_pcre replaces only first match
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

  // Ensure replace_pcre_all matches the longest match if many exist
  testUNSAT("""
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.+ (str.to.re "ab"))))
(assert (= y (str.replace_pcre_all x (pcre.+ (str.to_pcre "ab")) (pcre.replacement "a"))))
(assert (str.in.re y (re.comp (str.to.re "a"))))
(check-sat)
""")

  // The following two tests shows order in PCRE alternation matters for some situations.
  testFileSAT("pcre_precedence_sat") { (sm, _) => info(sm.toString) }

  testFileUNSAT("pcre_precedence_unsat")

  // pcre.group
  testUNSAT("""
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (str.to.re "ab")))
(assert (= y (str.replace_pcre
                 x
                 (pcre.++
                   (pcre.group (str.to_pcre "a"))
                   (pcre.group (str.to_pcre "b")))
                 (pcre.replacement 2 1 0))))
(assert (str.in.re y (re.comp (str.to.re "baab"))))
(check-sat)
""")

  testFileSAT("group_sc") { (sm, _) => info(sm.toString) }

  implicit class AtMostSubstring(s: String) {
    def atmostSubstring(idx: Int, len: Int): String = {
      if (0 <= idx && idx < s.length && 0 < len) s.substring(idx, idx + math.min(len, s.length - idx))
      else ""
    }
  }

  // Simple substr test (sat case)
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

  testFileUNSAT("indexof")

  testFileSAT("substr_zip_sat") { (sm, _) => info(sm.toString) }

  testFileUNSAT("substr_zip_unsat")

  // ???
  testSAT("""
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const w String)
(assert (not (= (str.len x) (str.len y))))
(assert (= z (str.substr x 0 (- (str.len x) 1))))
(assert (= w (str.substr y 0 (- (str.len y) 1))))
(assert (= (str.len z) (str.len w)))
(check-sat)
(get-model)
""") { (m, _) => () }

  testFileUNSAT("concat_prefix_suffix")

  testFileSAT("reverse_indexof_sat") { (m, _) => info(m.toString) }

  testFileUNSAT("reverse_indexof_unsat")

  // Using isFunctional, the following property will be provable:
  // 1. (str.replace_all x "a" "") and (str.replace_pcre_all x (pcre.+ (str.to_pcre "a")) (pcre.replacement ""))
  //    is equivalent for any x.
  // 2. (str.replace_all x "a" "b") and (str.replace_pcre_all x (pcre.+ (str.to_pcre "a")) (pcre.replacement "b"))
  //    is NOT equivalent, e.g. when x = "aa" the former is "bb" while the latter is "b".
}
