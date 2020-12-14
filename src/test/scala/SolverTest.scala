package com.github.kmn4.sst

import org.scalatest.funsuite._
import Solver._
import com.github.kmn4.sst.Constraint._

class SolverTest extends AnyFunSuite {
  def toOptionList(s: String): List[Option[Char]] = s.toList.map(c => if (c == '#') None else Some(c))
  def fromOptionList(l: List[Option[Char]]): String = l.map(_.getOrElse('#')).mkString
  def testTransduce[Q, X](
      sst: NSST[Q, Option[Char], Option[Char], X],
      w: String,
      expected: String*
  ) = assert(sst.transduce(toOptionList(w)) == expected.map(toOptionList).toSet)
  val alphabet = "ab".toSet
  test("constNSST") {
    {
      val n = constantNSST(2, "ab".toList, alphabet)
      testTransduce(n, "ba#b#", "ba#b#ab#")
      assert(n.transduce(toOptionList("ba#")) == Set.empty)
    }
  }
  test("replaceAllNSST") {
    {
      val n = ReplaceAll("aab", "b").toSolverSST(1, 0, alphabet)
      testTransduce(n, "aaabaab#", "aaabaab#abb#")
    }
  }

  test("ReplaceSome") {
    {
      val n = ReplaceSome("aab", "b").toSolverSST(1, 0, alphabet)
      assert(
        n.transduce(toOptionList("aaabaab#")).map(fromOptionList) == Set(
          "aaabaab#aaabaab#",
          "aaabaab#aaabb#",
          "aaabaab#abaab#",
          "aaabaab#abb#"
        )
      )
    }
  }

  test("concatNSST") {
    {
      // 2 := a0bb
      val n = concatNSST(2, List(Left("a".toList), Right(0), Left("bb".toList)), alphabet)
      assert(n.variables.size == 2)
      testTransduce(n, "ba#b#", "ba#b#ababb#")
      assert(n.transduce(toOptionList("ba#")) == Set.empty)
    }
    {
      // 2 := a1bb
      val n = concatNSST(2, List(Left("a".toList), Right(1), Left("bb".toList)), alphabet)
      assert(n.variables.size == 2)
      testTransduce(n, "ba#b#", "ba#b#abbb#")
      assert(n.transduce(toOptionList("ba#")) == Set.empty)
    }
    {
      // 2 := 10
      val n = concatNSST(2, List(Right(1), Right(0)), alphabet)
      assert(n.variables.size == 3)
      testTransduce(n, "ba#b#", "ba#b#bba#")
    }
    {
      // 2 := 00
      val n = concatNSST(2, List(Right(0), Right(0)), alphabet)
      assert(n.variables.size == 3)
      testTransduce(n, "ba#b#", "ba#b#baba#")
    }
  }
  test("insertNSST") {
    {
      val n = Insert(1, "aa").toSolverSST(2, 0, alphabet)
      testTransduce(n, "bb##", "bb##baab#")
      testTransduce(n, "##", "###")
    }
  }
  test("reverseNSST") {
    {
      val n = Reverse().toSolverSST(2, 0, alphabet)
      testTransduce(n, "ab##", "ab##ba#")
    }
  }
  test("atNSST") {
    {
      val n = At(1).toSolverSST(2, 0, alphabet)
      testTransduce(n, "aba##", "aba##b#")
      testTransduce(n, "ab#a#", "ab#a#b#")
      testTransduce(n, "a#b#", "a#b##")
    }
  }
  test("substrNSST") {
    {
      val n = Substr(1, 2).toSolverSST(2, 0, alphabet)
      testTransduce(n, "##", "###")
      testTransduce(n, "a##", "a###")
      testTransduce(n, "ab##", "ab##b#")
      testTransduce(n, "aba##", "aba##ba#")
      testTransduce(n, "abab##", "abab##ba#")
    }
  }

  test("takePrefixNSST") {
    {
      val n = TakePrefix().toSolverSST(2, 0, alphabet)
      assert(
        n.transduce(toOptionList("abb##")) == Set(
          "abb###",
          "abb##a#",
          "abb##ab#",
          "abb##abb#"
        ).map(toOptionList)
      )
    }
  }

  test("takeSuffixNSST") {
    {
      val n = TakeSuffix().toSolverSST(2, 0, alphabet)
      assert(
        n.transduce(toOptionList("abb##")) == Set(
          "abb###",
          "abb##b#",
          "abb##bb#",
          "abb##abb#"
        ).map(toOptionList)
      )
    }
  }

  test("UntilFirst") {
    val n = UntilFirst("aa").toSST(alphabet)
    assert(n.transduce("aa".toList) == Set("".toList))
    assert(n.transduce("baa".toList) == Set("b".toList))
    assert(n.transduce("abaa".toList) == Set("ab".toList))
    assert(n.transduce("aba".toList) == Set("aba".toList))
  }

  test("Copylessness") {
    assert(GeneralSubstr().toPairValuedSST(" ab".toSet).isCopyless)
    assert(IndexOfFromZero("aab").toPairValuedSST(" ab".toSet).isCopyless)
    assert(IndexOfFromZero("aab").toSolverSST(1, 0, " ab".toSet).isCopyless)
    assert(GeneralSubstr().toSolverSST(2, 0, " ab".toSet).isCopyless)
  }

//   test("Nondeterministic case 1") {
//     val input = """
// (declare-const x String)
// (declare-const y String)
// (declare-const z String)

// (assert (str.in.re x (re.++ (re.+ (str.to.re "a")) (re.+ (str.to.re "b")))))
// (assert (str.prefixof y x))
// (assert (str.prefixof z x))
// (assert (= (str.len x) (+ (str.len y) (str.len z))))
// (assert (= (str.len y) (str.len z)))
// (assert (str.in.re y (re.+ (str.to.re "a"))))
// (assert (str.in.re z (re.+ (str.to.re "b"))))
// (assert (> (str.len x) 7))
// """
//   }

//   test("hoge") {
//     val input = """
// (declare-const x0 String)
// (declare-const x1 String)
// (declare-const y0 String)
// (declare-const y1 String)

// (assert (= x1 (str.replaceall x0 "<sc>" "")))
// (assert (= y1 (str.replaceall y0 "<sc>" "")))
// (assert (< 0 (str.len x0)))
// (assert (< 0 (str.len y0)))
// (assert (= (str.len x1) (str.len y1)))
// (assert (= 10 (str.len x1)))
// """

  val constraintBase = "./constraints"
  def solveFile(fname: String)(check: Option[Map[String, String]] => Unit) = {
    import smtlib.trees.Commands.{Script, GetModel}
    import java.nio.file.FileSystems
    val path = FileSystems.getDefault().getPath(s"$constraintBase/$fname")
    val lexer = new smtlib.lexer.Lexer(new java.io.FileReader(path.toFile()))
    val parser = new smtlib.parser.Parser(lexer)
    val script = Script(parser.parseScript.commands.filter { case GetModel() => false; case _ => true })
    val solver = new Solver(())
    solver.executeTransPrint(script)
    check(solver.model())
  }
  test("deleteall.smt2") {
    solveFile("deleteall.smt2") {
      case Some(model) => {
        assert(model("x1") + model("y1") == model("xy"))
        assert(model("xy") == "<script>")
      }
      case None => fail()
    }
  }
  test("zhu/int3.smt2") {
    solveFile("zhu/int3.smt2") {
      case Some(model) => {
        val x0 = model("x0")
        val x1 = model("x1")
        val x2 = model("x2")
        assert(x1 == x0.reverse)
        assert(x2 == x1.replaceAll("ab", "c"))
        assert(x1.length() >= x2.length() + 5)
      }
      case None => fail()
    }
  }
  test("replace_some_1.smt2") {
    solveFile("nondet/replace_some_1.smt2") {
      case Some(model) => {
        val x = model("x")
        val y = model("y")
        info(s"x:${x},y:${y}")
        assert("a+".r.matches(x))
        assert("(:?ab)+".r.matches(y))
      }
      case None => fail()
    }
  }
  test("replace_some_2.smt2") {
    solveFile("nondet/replace_some_2.smt2") {
      case Some(model) => fail()
      case None        => {}
    }
  }
  test("ab_star_prefix.smt2") {
    solveFile("nondet/ab_star_prefix.smt2") {
      case Some(model) => fail()
      case None        => {}
    }
  }
}
