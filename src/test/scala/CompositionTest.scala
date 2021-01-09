package com.github.kmn4.sst

import scala.math.max

import org.scalatest.flatspec._

class CompositionTest extends AnyFlatSpec {
  implicit val logger = NopLogger
  val nsst = NSST(
    Set(0, 1),
    Set('X', 'Y'),
    List(
      (0, 'a', List((0, List("X:Xa", "Y:aY")))),
      (0, 'b', List((1, List("X:Xb", "Y:bY")))),
      (1, 'a', List((0, List("X:Xa", "Y:aY")))),
      (1, 'b', List((1, List("X:Xb", "Y:bY"))))
    ),
    0,
    List((1, "XaY"))
  )
  def maxTransition[Q, A, B, X](nsst: NSST[Q, A, B, X]): Int = {
    nsst.delta.foldLeft(0) { case (acc, (k, v)) => max(acc, v.size) }
  }

  // a^n ↦ { w#w | len(w) == n }
  val alur21 = NSST(
    Set(0),
    Set('X', 'Y'),
    List(
      (
        0,
        'a',
        List(
          (0, List("X:Xa", "Y:Ya")),
          (0, List("X:Xb", "Y:Yb"))
        )
      )
    ),
    0,
    List((0, "X#Y"))
  )

  val alur21Three = NSST(
    Set(0),
    Set('X', 'Y', 'Z'),
    List(
      (
        0,
        'a',
        List(
          (0, List("X:Xa", "Y:Ya", "Z:Za")),
          (0, List("X:Xb", "Y:Yb", "Z:Zb"))
        )
      )
    ),
    0,
    List((0, "X#Y#Z"))
  )

  // Doubles 'a's in a given string if it has even number of them,
  // and do nothing otherwise.
  val doubleAsIfEvenSST = NSST(
    Set(0, 11, 10, 21, 20),
    List('X'),
    List(
      (0, 'a', List((11, List("X:Xa")))),
      (0, 'a', List((21, List("X:Xaa")))),
      (0, 'b', List((10, List("X:Xb")))),
      (0, 'b', List((20, List("X:Xb")))),
      (11, 'a', List((10, List("X:Xa")))),
      (10, 'a', List((11, List("X:Xa")))),
      (21, 'a', List((20, List("X:Xaa")))),
      (20, 'a', List((21, List("X:Xaa")))),
      (11, 'b', List((11, List("X:Xb")))),
      (10, 'b', List((10, List("X:Xb")))),
      (21, 'b', List((21, List("X:Xb")))),
      (20, 'b', List((20, List("X:Xb")))),
      (11, '#', List((11, List("X:X#")))),
      (10, '#', List((10, List("X:X#")))),
      (21, '#', List((21, List("X:X#")))),
      (20, '#', List((20, List("X:X#"))))
    ),
    0,
    Set((11, "X"), (20, "X"))
  )

  "Transducers" should "transduce correctly" in {
    assert(alur21.transduce("aaaaa".toList).size == List.fill(5)(2).product)
  }

  // {a, b}^* \ {ε} ∋ w ↦ {u | #u = #w or #u = 2#w} ⊂ {a, b}^*
  val sameOrTwiceLen = NSST(
    Set(0, 1, 2),
    Set('X', 'Y'),
    List(
      (
        0,
        'a',
        List(
          (1, List("X:Xa", "Y:Ya")),
          (1, List("X:Xa", "Y:Yb")),
          (1, List("X:Xb", "Y:Ya")),
          (1, List("X:Xb", "Y:Yb")),
          (2, List("X:Xa", "Y:Ya")),
          (2, List("X:Xa", "Y:Yb")),
          (2, List("X:Xb", "Y:Ya")),
          (2, List("X:Xb", "Y:Yb"))
        )
      ),
      (
        0,
        'b',
        List(
          (1, List("X:Xa", "Y:Ya")),
          (1, List("X:Xa", "Y:Yb")),
          (1, List("X:Xb", "Y:Ya")),
          (1, List("X:Xb", "Y:Yb")),
          (2, List("X:Xa", "Y:Ya")),
          (2, List("X:Xa", "Y:Yb")),
          (2, List("X:Xb", "Y:Ya")),
          (2, List("X:Xb", "Y:Yb"))
        )
      ),
      (
        1,
        'a',
        List(
          (1, List("X:Xa", "Y:Ya")),
          (1, List("X:Xa", "Y:Yb")),
          (1, List("X:Xb", "Y:Ya")),
          (1, List("X:Xb", "Y:Yb"))
        )
      ),
      (
        1,
        'b',
        List(
          (1, List("X:Xa", "Y:Ya")),
          (1, List("X:Xa", "Y:Yb")),
          (1, List("X:Xb", "Y:Ya")),
          (1, List("X:Xb", "Y:Yb"))
        )
      ),
      (
        2,
        'a',
        List(
          (2, List("X:Xa", "Y:Ya")),
          (2, List("X:Xa", "Y:Yb")),
          (2, List("X:Xb", "Y:Ya")),
          (2, List("X:Xb", "Y:Yb"))
        )
      ),
      (
        2,
        'b',
        List(
          (2, List("X:Xa", "Y:Ya")),
          (2, List("X:Xa", "Y:Yb")),
          (2, List("X:Xb", "Y:Ya")),
          (2, List("X:Xb", "Y:Yb"))
        )
      )
    ),
    0,
    List((1, "X"), (2, "XY"))
  )
  // w ↦ ww
  val doubles = NSST(
    Set(0),
    Set('X', 'Y'),
    List((0, 'a', List((0, List("X:Xa", "Y:Ya"))))),
    0,
    List((0, "XY"))
  )
  "Construction of MSST" should "be done correctly" in {
    {
      // val composed = SST.composeNSSTsBackward(doubles.toSingleOutput, sameOrTwiceLen.toSingleOutput)
      val composed = NSST.composeNsstsToMsst(doubles, doubles)
      info(s"Number of states: ${composed.states.size}")
      assert(composed.transduce("".toList) == Set("".toList))
      assert(composed.transduce("a".toList) == Set("aaaa".toList))
    }

    {
      assert(
        alur21Three.transduce("aa".toList) ==
          Set("aa#aa#aa", "ab#ab#ab", "ba#ba#ba", "bb#bb#bb").map(_.toList)
      )
      assert(
        doubleAsIfEvenSST.transduce("aa#aa#aa".toList) ==
          Set("aaaa#aaaa#aaaa".toList)
      )
      assert(
        doubleAsIfEvenSST.transduce("ab#ab#ab".toList) ==
          Set("ab#ab#ab".toList)
      )
      val composed = NSST.composeNsstsToMsst(alur21Three, doubleAsIfEvenSST)
      assert(
        composed.transduce("aa".toList) ==
          Set("aaaa#aaaa#aaaa", "ab#ab#ab", "ba#ba#ba", "bb#bb#bb").map(_.toList)
      )

    }

    {
      assert(doubles.transduce(List('a')) == Set("aa".toList))
      assert(
        sameOrTwiceLen.transduce("aa".toList) ==
          Set(
            "aa",
            "ab",
            "ba",
            "bb",
            "aaaa",
            "aaab",
            "aaba",
            "aabb",
            "abaa",
            "abab",
            "abba",
            "abbb",
            "bbbb",
            "bbba",
            "bbab",
            "bbaa",
            "babb",
            "baba",
            "baab",
            "baaa"
          ).map(_.toList)
      )
      val n1AfterSimple = NSST.composeNsstsToMsst(doubles, sameOrTwiceLen)
      info(s"Number of states of [sameOrTwiceLen after doubles]: ${n1AfterSimple.states.size}")
      assert(
        n1AfterSimple.transduce("a".toList) ==
          Set(
            "aa",
            "ab",
            "ba",
            "bb",
            "aaaa",
            "aaab",
            "aaba",
            "aabb",
            "abaa",
            "abab",
            "abba",
            "abbb",
            "bbbb",
            "bbba",
            "bbab",
            "bbaa",
            "babb",
            "baba",
            "baab",
            "baaa"
          ).map(_.toList)
      )
      val n1AfterN1 = NSST.composeNsstsToMsst(sameOrTwiceLen, sameOrTwiceLen)
      info(
        s"Number of states of [sameOrTwiceLen after sameOrTwiceLen]: ${n1AfterSimple.states.size}"
      )
      assert(
        n1AfterN1.transduce("a".toList) ==
          Set(
            "a",
            "b",
            "aa",
            "ab",
            "ba",
            "bb",
            "aaaa",
            "aaab",
            "aaba",
            "aabb",
            "abaa",
            "abab",
            "abba",
            "abbb",
            "bbbb",
            "bbba",
            "bbab",
            "bbaa",
            "babb",
            "baba",
            "baab",
            "baaa"
          ).map(_.toList)
      )
    }

  }

  "Composition of two NSSTs" should "be done correctly" in {
    val composed = sameOrTwiceLen compose sameOrTwiceLen
    info(s"Number of states: ${composed.states.size}")
    info(s"Max number of transition destinations: ${maxTransition(composed)}")
    assert(composed.isCopyless)
    assert(composed.transduce("".toList) == Set())
    assert(
      composed.transduce("a".toList) ==
        Set(
          "a",
          "b",
          "aa",
          "ab",
          "ba",
          "bb",
          "aaaa",
          "aaab",
          "aaba",
          "aabb",
          "abaa",
          "abab",
          "abba",
          "abbb",
          "bbbb",
          "bbba",
          "bbab",
          "bbaa",
          "babb",
          "baba",
          "baab",
          "baaa"
        ).map(_.toList)
    )
  }
}
