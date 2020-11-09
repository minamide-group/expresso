package com.github.kmn4.sst

import org.scalatest.funsuite._
import scala.util.Random.{nextInt}

class TestFunctionalness extends AnyFunSuite {
  import Constraint._
  test("sstEndsWith meets spec") {
    val abc = "abc".toSet
    val ab = "ab".toSet
    val rev = Reverse().toSST(abc)
    val uf = UntilFirst("a").toSST(abc)
    val revE = rev.sstEndsWith(ab)
    val ufE = uf.sstEndsWith(ab)
    def endsWith(chars: Set[Char])(w: List[Char]): Set[List[Char]] = {
      for (i <- 0 until w.length if chars(w(i))) yield w.take(i + 1)
    }.toSet
    val endsWithAB = endsWith(ab) _
    for (i <- 0 until 100) {
      val cs = for (_ <- 0 until nextInt(10)) yield "abc" (nextInt(3))
      val w = cs.toList
      assert(rev.transduce(w).flatMap(endsWithAB) == revE.transduce(w))
      assert(uf.transduce(w).flatMap(endsWithAB) == ufE.transduce(w))
    }
    for (i <- 0 until 100) {
      val n = TestRandom.randomNsstCustomized()
      val e = n.sstEndsWith("a".toSet)
      for (j <- 0 until 10) {
        val cs = for (_ <- 0 until nextInt(10)) yield "ab" (nextInt(2))
        val w = cs.toList
        assert(n.transduce(w).flatMap(endsWith("a".toSet)) == e.transduce(w))
      }
    }
  }
  test("lengthCA counts length") {
    for (i <- 0 until 100) {
      val n = TestRandom.randomNsstCustomized()
      val ca = n.lengthCA
      for (i <- 0 until 100) {
        val cs = for (_ <- 0 until nextInt(10)) yield "ab" (nextInt(2))
        val w = cs.toList
        assert(n.transduce(w).map(_.length) == ca.transduce(w.map(Some.apply) :+ None))
      }
    }
  }
  test("isFunctional correctly decides functionalness for each solver SST") {
    val alpha = "ab".toSet
    assert(At(0).toSST(alpha).isFunctional)
    assert(At(1).toSST(alpha).isFunctional)
    assert(Insert(0, "hoge").toSST(alpha).isFunctional)
    assert(Insert(0, "").toSST(alpha).isFunctional)
    assert(Insert(1, "aa").toSST(alpha).isFunctional)
    assert(ReplaceAll("", "").toSST(alpha).isFunctional)
    assert(ReplaceAll("ab", "ba").toSST(alpha).isFunctional)
    assert(ReplaceAll("aa", "").toSST(alpha).isFunctional)
    assert(Reverse().toSST(alpha).isFunctional)
    assert(UntilFirst("").toSST(alpha).isFunctional)
    assert(UntilFirst("aa").toSST(alpha).isFunctional)
    assert(UntilFirst("ab").toSST(alpha).isFunctional)
    assert(!TakePrefix().toSST(alpha).isFunctional)
    assert(!TakeSuffix().toSST(alpha).isFunctional)
  }
}
