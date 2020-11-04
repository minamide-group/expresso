package com.github.kmn4.sst

import org.scalatest.funsuite._
import Solver._
import com.github.kmn4.sst.Constraint._

class TestSolver extends AnyFunSuite {
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
}
