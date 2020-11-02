package com.github.kmn4.sst

import org.scalatest.funsuite._
import Solver._
import com.github.kmn4.sst.Constraint.SLConstraint

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
      val n = replaceAllNSST("aab".toList, "b".toList, 1, 0, alphabet)
      testTransduce(n, "aaab#", "aaab#ab#")
    }
  }
  test("preppendAppendNSST") {
    {
      val n = preppendAppendNSST(2, 0, "a".toList, "bb".toList, alphabet)
      testTransduce(n, "ba#b#", "ba#b#ababb#")
      assert(n.transduce(toOptionList("ba#")) == Set.empty)
    }
    {
      val n = preppendAppendNSST(2, 1, "a".toList, "bb".toList, alphabet)
      testTransduce(n, "ba#b#", "ba#b#abbb#")
      assert(n.transduce(toOptionList("ba#")) == Set.empty)
    }
  }
  test("insertNSST") {
    {
      val n = insertNSST(2, 0, 1, "aa".toList, alphabet)
      testTransduce(n, "bb##", "bb##baab#")
      testTransduce(n, "##", "###")
    }
  }
  test("reverseNSST") {
    {
      val n = reverseNSST(2, 0, alphabet)
      testTransduce(n, "ab##", "ab##ba#")
    }
  }
  test("atNSST") {
    {
      val n = atNSST(2, 0, 1, alphabet)
      testTransduce(n, "aba##", "aba##b#")
      testTransduce(n, "ab#a#", "ab#a#b#")
      testTransduce(n, "a#b#", "a#b##")
    }
  }
  test("substrNSST") {
    {
      val n = substrNSST(2, 0, 1, 2, alphabet)
      testTransduce(n, "##", "###")
      testTransduce(n, "a##", "a###")
      testTransduce(n, "ab##", "ab##b#")
      testTransduce(n, "aba##", "aba##ba#")
      testTransduce(n, "abab##", "abab##ba#")
    }
  }

  test("takePrefixNSST") {
    {
      val n = takePrefixNSST(2, 0, alphabet)
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
      val n = takeSuffixNSST(2, 0, alphabet)
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

  test("Nondeterministic case 1") {
    val input = """
(declare-const x String)
(declare-const y String)
(declare-const z String)

(assert (str.in.re x (re.++ (re.+ (str.to.re "a")) (re.+ (str.to.re "b")))))
(assert (= y (str.take_prefix x)))
(assert (= z (str.take_suffix x)))
(assert (= (str.len x) (+ (str.len y) (str.len z))))
(assert (= (str.len y) (str.len z)))
(assert (str.in.re y (re.+ (str.to.re "a"))))
(assert (str.in.re z (re.+ (str.to.re "b"))))
(assert (> (str.len x) 7))
"""
    val s = System.nanoTime()
    val fs = smtlib2.Parser.parse(input).map(smtlib2.Form.fromSExpr)
    val c = SLConstraint.fromForms(fs)
    val (sst, Some(nft)) = compileConstraint(c, Set('a', 'b', ' '))
    info(sst.transduce(toOptionList("aaabbb#")).map(fromOptionList).toString())
    // Main.parseAndSolve(input) match {
    //   case None => fail()
    //   case Some(m) => {
    //     val x = m("x")
    //     val y = m("y")
    //     val z = m("z")
    //     assert(x.length == y.length + z.length)
    //     assert(y.length == z.length)
    //     info(s"""x: "$x"""")
    //     info(s"""y: "$y"""")
    //     info(s"""z: "$z"""")
    //   }
    // }
    info(s"elapsed: ${(System.nanoTime() - s) / 1000000} ms")
  }

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
//     Main.parseAndSolve(input) match {
//       case None => fail
//       case Some(m) => {
//         info(s"""x0: ${m("x0")}""")
//         info(s"""x1: ${m("x1")}""")
//         info(s"""y0: ${m("y0")}""")
//         info(s"""y1: ${m("y1")}""")
//       }
//     }
//   }
}
