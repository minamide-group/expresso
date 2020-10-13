package com.github.kmn4.sst

import org.scalatest.funsuite._
import Solver._

class TestSolver extends AnyFunSuite {
  def toOptionList(s: String): List[Option[Char]] = s.toList.map(c => if (c == '#') None else Some(c))
  def fromOptionList(l: List[Option[Char]]): String = l.map(_.getOrElse('#')).mkString
  def testTransduce[Q, X](
      sst: NSST[Q, Option[Char], Option[Char], X],
      w: String,
      expected: String*
  ) = assert(sst.transduce(toOptionList(w)) == expected.map(toOptionList).toSet)
  val alphabet = "ab".toSet
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

}
