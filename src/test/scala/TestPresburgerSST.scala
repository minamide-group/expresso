package com.github.kmn4.sst

import org.scalatest.funsuite.AnyFunSuite

import com.github.kmn4.sst.Presburger._

class TestPresburgerSST extends AnyFunSuite {
  def testEquiv[A, B, I](t1: StringIntTransducer[A, B, I], t2: StringIntTransducer[A, B, I])(
      cases: (Seq[A], Map[I, Int])*
  ) = cases.foreach {
    case (w, i) =>
      val r1 = t1.transduce(w, i)
      val r2 = t2.transduce(w, i)
      if (r1 == r2) succeed
      else fail(s"$w:\n\tt1:\t${r1}\n\tt2\t${r2}")
  }

  def testExamples[A, B, I](t: StringIntTransducer[A, B, I])(cases: ((Seq[A], Map[I, Int]), Seq[B])*) =
    cases.foreach {
      case ((w, i), o) =>
        val res = t.transduce(w, i)
        if (res.size != 1) fail(s"$w,$i:\toutput size is not one but ${res.size}")
        else if (res.head != o) fail(s"$w:\t\n\texpected:\t${o}\n\tgot:\t${res.head}")
        else succeed
    }

  def substr(i: String, l: String) = PresburgerSST.substr("abcd".toSet)(i, l)
  val substr1 = substr("i", "l")
  test("substr transduction") {
    assert(substr1.transduce("abab".toSeq, Map("i" -> 0, "l" -> 2)) == Set("ab".toSeq))
    assert(substr1.transduce("abab".toSeq, Map("i" -> 1, "l" -> 2)) == Set("ba".toSeq))
    assert(substr1.transduce("bba".toSeq, Map("i" -> 1, "l" -> 2)) == Set("ba".toSeq))
    assert(substr1.transduce("aa".toSeq, Map("i" -> -1, "l" -> 2)) == Set("".toSeq))
    assert(substr1.transduce("aa".toSeq, Map("i" -> 3, "l" -> 2)) == Set("".toSeq))
    assert(substr1.transduce("aa".toSeq, Map("i" -> 0, "l" -> -2)) == Set("".toSeq))
  }
  val substr2 = substr("j", "k")
  test("Compose two substr") {
    val doubled = substr1.composeNsstsToMsst(substr1, substr2)(NopLogger)
    implicit def conv(t: (Int, Int, Int, Int)): Map[String, Int] = {
      val (i, l, j, k) = t
      Map("i" -> i, "l" -> l, "j" -> j, "k" -> k)
    }
    val cases: Seq[((Seq[Char], Map[String, Int]), Seq[Char])] = Seq(
      (("abab", (0, 3, 1, 2)), "ba"),
      (("abab", (2, 3, 1, 2)), "b"),
      (("abab", (-2, 3, 1, 2)), ""),
      (("abab", (2, -3, 1, 2)), ""),
      (("abab", (2, 3, 2, 0)), ""),
      (("abab", (2, 3, -2, 0)), ""),
      (("abab", (2, 3, 2, -1)), ""),
      (("aabb", (1, 3, 0, 2)), "ab"),
      (("aabb", (0, 4, 0, 4)), "aabb"),
      (("abcd", (0, 4, 0, 4)), "abcd")
    )
    testExamples(doubled)(cases: _*)
    val lc = doubled.toLocallyConstrainedAffineParikhSST
    val equivCases = cases.map { case ((w, i), _) => (w, i) }
    testEquiv(lc, doubled)(equivCases: _*)
    val ap = lc.toAffineParikhSST
    testEquiv(ap, lc)(equivCases: _*)
    val p = ap.toPresburgerSST
    testEquiv(p, ap)(equivCases: _*)
    val direct = substr1 compose substr2
    testExamples(direct)(cases: _*)
  }

  test("Compose three substr") {
    val substr3 = substr("s", "t")
    implicit def conv(n: (Int, Int, Int, Int, Int, Int)): Map[String, Int] = {
      val (i, l, j, k, s, t) = n
      Map("i" -> i, "l" -> l, "j" -> j, "k" -> k, "s" -> s, "t" -> t)
    }
    val cases: Seq[((Seq[Char], Map[String, Int]), Seq[Char])] = Seq(
      (("abcd", (0, 3, 1, 2, 1, 1)), "c"),
      (("abcd", (0, 4, 0, 4, 0, 4)), "abcd")
    )
    val composed = substr1 compose substr2 compose substr3
    testExamples(composed)(cases: _*)
  }
}
