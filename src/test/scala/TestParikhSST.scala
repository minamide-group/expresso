package com.github.kmn4.sst

import org.scalatest.funsuite.AnyFunSuite

import com.github.kmn4.sst.Presburger._

class TestParikhSST extends AnyFunSuite {
  def testEquiv[A, B, I](t1: StringIntTransducer[A, B, I], t2: StringIntTransducer[A, B, I])(
      cases: Seq[(Seq[A], Map[I, Int])]
  ) = cases.foreach {
    case (w, i) =>
      val r1 = t1.transduce(w, i)
      val r2 = t2.transduce(w, i)
      if (r1 == r2) succeed
      else fail(s"$w:\n\tt1:\t${r1}\n\tt2\t${r2}")
  }

  def testExamples[A, B, I](t: StringIntTransducer[A, B, I])(cases: Seq[(Seq[A], Map[I, Int], Seq[B])]) =
    cases.foreach {
      case (w, i, o) =>
        val res = t.transduce(w, i)
        if (res.size != 1) fail(s"$w,$i:\toutput size is not one but ${res.size}")
        else if (res.head != o) fail(s"$w:\t\n\texpected:\t${o}\n\tgot:\t${res.head}")
        else succeed
    }

  def substr(i: String, l: String) = ParikhSST.substr("abcd".toSet)(i, l)
  val substr1 = substr("i", "l")
  test("substr transduction") {
    implicit def conv(t: (Int, Int)): Map[String, Int] = t match {
      case (i, l) => Map("i" -> i, "l" -> l)
    }
    testExamples(substr1)(
      Seq(
        ("abab", (0, 2), "ab"),
        ("abab", (1, 2), "ba"),
        ("bba", (1, 2), "ba"),
        ("aa", (-1, 2), ""),
        ("aa", (3, 2), ""),
        ("aa", (0, -2), "")
      )
    )
  }
  val substr2 = substr("j", "k")
  test("Compose two substr") {
    val doubled = substr1.composeNsstsToMsst(substr1, substr2)(NopLogger)
    implicit def conv(t: (Int, Int, Int, Int)): Map[String, Int] = t match {
      case (i, l, j, k) => Map("i" -> i, "l" -> l, "j" -> j, "k" -> k)
    }
    val cases: Seq[(Seq[Char], Map[String, Int], Seq[Char])] = Seq(
      ("abab", (0, 3, 1, 2), "ba"),
      ("abab", (2, 3, 1, 2), "b"),
      ("abab", (-2, 3, 1, 2), ""),
      ("abab", (2, -3, 1, 2), ""),
      ("abab", (2, 3, 2, 0), ""),
      ("abab", (2, 3, -2, 0), ""),
      ("abab", (2, 3, 2, -1), ""),
      ("aabb", (1, 3, 0, 2), "ab"),
      ("aabb", (0, 4, 0, 4), "aabb"),
      ("abcd", (0, 4, 0, 4), "abcd")
    )
    val lc = doubled.toLocallyConstrainedAffineParikhSST
    val equivCases = cases.map { case (w, i, _) => (w, i) }
    testEquiv(lc, doubled)(equivCases)
    val ap = lc.toAffineParikhSST
    testEquiv(ap, lc)(equivCases)
    val p = ap.toParikhSST
    testEquiv(p, ap)(equivCases)
    val direct = substr1 compose substr2
    testExamples(direct)(cases)
  }

  test("Compose three substr") {
    val substr3 = substr("s", "t")
    implicit def conv(t: (Int, Int, Int, Int, Int, Int)): Map[String, Int] = t match {
      case (i, l, j, k, s, t) => Map("i" -> i, "l" -> l, "j" -> j, "k" -> k, "s" -> s, "t" -> t)
    }
    val cases: Seq[(Seq[Char], Map[String, Int], Seq[Char])] = Seq(
      ("abcd", (0, 3, 1, 2, 1, 1), "c"),
      ("abcd", (0, 4, 0, 4, 0, 4), "abcd")
    )
    val composed = substr1 compose substr2 compose substr3
    testExamples(composed)(cases)
  }

  test("Compose replaceAll and substr") {
    val replaceAll = Constraint.ReplaceAll("aab", "abc").toSST("abcd".toSet).toParikhSST[String, String]
    val composed = replaceAll compose substr1
    implicit def conv(n: (Int, Int)): Map[String, Int] = n match {
      case (i, l) => Map("i" -> i, "l" -> l)
    }
    val cases: Seq[(Seq[Char], Map[String, Int], Seq[Char])] = Seq(
      ("aabc", (0, 4), "abcc"),
      ("aabc", (0, 3), "abc"),
      ("aabc", (3, 10), "c"),
      ("aabc", (-1, 5), "")
    )
    testExamples(composed)(cases)
  }

  def indexOf(word: String, i: String) = ParikhSST.indexOf("abcd".toSet)(word, i)

  test("Compose replaceAll and indexOf") {
    val replaceAll = Constraint.ReplaceAll("aab", "abc").toSST("abcd".toSet).toParikhSST[String, String]
    val indexOfAB = indexOf("ab", "i")
    testExamples(indexOfAB)(
      Seq(
        ("aab", Map("i" -> 1), "a")
      )
    )
    val composed = replaceAll compose indexOfAB
    Seq(
      ("aab", 0, Some("")),
      ("aab", 1, None),
      ("aab", 2, None),
      ("aab", -1, None),
      ("aaaab", 2, Some("aa"))
    ).foreach {
      case (in, i, out) =>
        val got = composed.transduce(in, Map("i" -> i))
        assert(got.size <= 1)
        assert(got.headOption == out.map(_.toSeq))
    }
  }
}