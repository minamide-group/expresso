package com.github.kmn4.sst

import org.scalatest.funsuite.AnyFunSuite

class TestPresburgerSST extends AnyFunSuite {
  import Presburger._
  def substr(iName: String, lName: String): PresburgerSST[Int, Char, Char, Int, Int, String] = {
    val X = 0
    type T = Term[Either[String, Int]]
    val i: T = Var(Left(iName))
    val l: T = Var(Left(lName))
    val d: T = Var(Right(0))
    val r0: T = Var(Right(1))
    val r1: T = Var(Right(2))
    val zero: T = Const(0)
    val idxOutOrNegLen = Disj(Seq(Lt(i, zero), Ge(i, d), Le(l, zero)))
    val inSet = "ab".toSet
    val unit: (Concepts.Update[Int, Char], PresburgerSST.IUpdate[Int]) =
      (Map(X -> List(Cop1(X))), (1 to 2).map(h => h -> 0).toMap + (0 -> 1))
    val edges = inSet
      .flatMap { a =>
        val (unitX, unitH) = unit
        val seek = (unitX, unitH + (2 -> 1))
        val take = (Map(X -> List(Cop1(X), Cop2(a))), unitH + (1 -> 1))
        val ignore = unit
        Iterable(
          (0, a, seek, 0),
          (0, a, take, 1),
          (1, a, take, 1),
          (1, a, ignore, 2),
          (2, a, ignore, 2)
        )
      }
      .map { case (q, a, (mx, mh), r) => (q, a, mx, mh, r) }
    PresburgerSST[Int, Char, Char, Int, Int, String](
      Set(0, 1, 2),
      inSet,
      Set(X),
      Set(0, 1, 2),
      Set("i", "l"),
      edges,
      0,
      (0 to 2).map((_, List(Cop1(X)), (0 to 2).map(h => h -> 0).toMap)).toSet,
      Seq(
        Implies(idxOutOrNegLen, Eq(r0, zero)),
        Implies(Conj(Seq(Not(idxOutOrNegLen), Le(l, Sub(d, i)))), Conj(Seq(Eq(r1, i), Eq(r0, l)))),
        Implies(Conj(Seq(Not(idxOutOrNegLen), Gt(l, Sub(d, i)))), Conj(Seq(Eq(r1, i), Eq(r0, Sub(d, i)))))
      )
    )
  }

  val substr1 = substr("i", "l")
  test("transduce") {
    assert(substr1.transduce("abab".toSeq, Map("i" -> 0, "l" -> 2)) == Set("ab".toSeq))
    assert(substr1.transduce("abab".toSeq, Map("i" -> 1, "l" -> 2)) == Set("ba".toSeq))
    assert(substr1.transduce("bba".toSeq, Map("i" -> 1, "l" -> 2)) == Set("ba".toSeq))
    assert(substr1.transduce("aa".toSeq, Map("i" -> -1, "l" -> 2)) == Set("".toSeq))
    assert(substr1.transduce("aa".toSeq, Map("i" -> 3, "l" -> 2)) == Set("".toSeq))
    assert(substr1.transduce("aa".toSeq, Map("i" -> 0, "l" -> -2)) == Set("".toSeq))
  }
  val substr2 = substr("j", "k")
  test("compose") {
    // val composed: PresburgerSST[Int, Char, Char, Int, Int, String] = substr1 compose substr2
    val composed = substr1.composeNsstsToMsst(substr1, substr2)(NopLogger)
    assert(composed.transduce("abab".toSeq, Map("i" -> 0, "l" -> 3, "j" -> 1, "k" -> 2)) == Set("ba".toSeq))
    assert(composed.transduce("abab".toSeq, Map("i" -> 2, "l" -> 3, "j" -> 1, "k" -> 2)) == Set("b".toSeq))
    assert(composed.transduce("abab".toSeq, Map("i" -> -2, "l" -> 3, "j" -> 1, "k" -> 2)) == Set("".toSeq))
    assert(composed.transduce("abab".toSeq, Map("i" -> 2, "l" -> -3, "j" -> 1, "k" -> 2)) == Set("".toSeq))
    assert(composed.transduce("abab".toSeq, Map("i" -> 2, "l" -> 3, "j" -> 2, "k" -> 0)) == Set("".toSeq))
    assert(composed.transduce("abab".toSeq, Map("i" -> 2, "l" -> 3, "j" -> -2, "k" -> 0)) == Set("".toSeq))
    assert(composed.transduce("abab".toSeq, Map("i" -> 2, "l" -> 3, "j" -> 2, "k" -> -1)) == Set("".toSeq))
  }
}
