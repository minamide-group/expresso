package com.github.kmn4.sst

import org.scalatest.flatspec._
import org.scalatest.concurrent.TimeLimits._
import org.scalatest.time._
import scala.math.max

class TestComposition extends AnyFlatSpec {
  val nsst = NSST(
    Set(0, 1),
    Set('X', 'Y'),
    List((0, 'a', List((0, List("X:Xa", "Y:aY")))),
         (0, 'b', List((1, List("X:Xb", "Y:bY")))),
         (1, 'a', List((0, List("X:Xa", "Y:aY")))),
         (1, 'b', List((1, List("X:Xb", "Y:bY"))))),
    0,
    List((1, "XaY"))
  )
  val nft = NFT(
    Set(0, 1),
    List((0, 'a', 1, ""),
         (0, 'b', 0, "bb"),
         (1, 'a', 1, "aa"),
         (1, 'b', 0, "")),
    0,
    Set(1)
  )

  def maxTransition[Q, A, B, X](nsst: NSST[Q, A, B, X]): Int = {
    nsst.edges.foldLeft(0){ case (acc, (k, v)) => max(acc, v.size) }
  }

  // a^n ↦ { w#w | len(w) == n }
  val alur21 = NSST(
    Set(0),
    Set('X', 'Y'),
    List((0, 'a', List(
            (0, List("X:Xa", "Y:Ya")),
            (0, List("X:Xb", "Y:Yb")),
          ))),
    0,
    List((0, "X#Y"))
  )

  val alur21Three = NSST(
    Set(0),
    Set('X', 'Y', 'Z'),
    List((0, 'a', List(
            (0, List("X:Xa", "Y:Ya", "Z:Za")),
            (0, List("X:Xb", "Y:Yb", "Z:Zb")),
          ))),
    0,
    List((0, "X#Y#Z"))
  )

  // Doubles 'a's in a given string if it has even number of them,
  // and do nothing otherwise.
  val doubleAsIfEven = NFT(
    Set(0, 11, 10, 21, 20),
    List(
      (0, 'a', 11, "a"),
      (0, 'a', 21, "aa"),
      (0, 'b', 10, "b"),
      (0, 'b', 20, "b"),
      (11, 'a', 10, "a"),
      (10, 'a', 11, "a"),
      (21, 'a', 20, "aa"),
      (20, 'a', 21, "aa"),
      (11, 'b', 11, "b"),
      (10, 'b', 10, "b"),
      (21, 'b', 21, "b"),
      (20, 'b', 20, "b"),
      (11, '#', 11, "#"),
      (10, '#', 10, "#"),
      (21, '#', 21, "#"),
      (20, '#', 20, "#")
    ),
    0,
    Set(11, 20)
  )

  "Transducers" should "transduce correctly" in {
    assert(alur21.transduce("aaaaa".toList).size == List.fill(5)(2).product)
    assert(doubleAsIfEven.transduce("ababab".toList) == Set("ababab".toList))
    assert(doubleAsIfEven.transduce("baab".toList) == Set("baaaab".toList))
  }

  "Composition" should "" in {
    val composed = NSST.composeNsstAndNft(nsst, nft)
    info(s"Number of states: ${composed.states.size}")
    info(s"Max number of transition destinations: ${maxTransition(composed)}")
    assert(composed.transduce("abb".toList) == Set("bbbb".toList))
    assert(composed.isCopyless)
  }

  "Composition of Alur's exmaple 2.1 and doubleAsIfEven" should
  "map string w to w'#w' where w' == w[aa/a]" in {
    val composed = NSST.composeNsstAndNft(alur21, doubleAsIfEven)
    info(s"Number of states: ${composed.states.size}")
    info(s"Max number of transition destinations: ${maxTransition(composed)}")
    assert(composed.transduce("aa".toList) ==
             Set("aaaa#aaaa", "aab#aab", "baa#baa", "bb#bb").map(_.toList))
    assert(composed.isCopyless)
  }

  "Composition of a variant of Alur's ex 2.1 and doubleAsIfEven" should
  "terminate in reasonable time and transduce correctly" in {
    val composed = NSST.composeNsstAndNft(alur21Three, doubleAsIfEven)
    info(s"Number of states: ${composed.states.size}")
    info(s"Max number of transition destinations: ${maxTransition(composed)}")
    assert(composed.transduce("aa".toList) ==
             Set("aaaa#aaaa#aaaa", "ab#ab#ab", "ba#ba#ba", "bb#bb#bb").map(_.toList))
    assert(composed.isCopyless)
  }

  "Composition of two NSSTs" should "be done correctly" in {
    val n1 = NSST(
      Set(0, 1, 2),
      Set('X', 'Y'),
      List(
        (0, 'a', List(
           (1, List("X:Xa", "Y:Ya")),
           (1, List("X:Xa", "Y:Yb")),
           (1, List("X:Xb", "Y:Ya")),
           (1, List("X:Xb", "Y:Yb")),
           (2, List("X:Xa", "Y:Ya")),
           (2, List("X:Xa", "Y:Yb")),
           (2, List("X:Xb", "Y:Ya")),
           (2, List("X:Xb", "Y:Yb")))),
        (0, 'b', List(
           (1, List("X:Xa", "Y:Ya")),
           (1, List("X:Xa", "Y:Yb")),
           (1, List("X:Xb", "Y:Ya")),
           (1, List("X:Xb", "Y:Yb")),
           (2, List("X:Xa", "Y:Ya")),
           (2, List("X:Xa", "Y:Yb")),
           (2, List("X:Xb", "Y:Ya")),
           (2, List("X:Xb", "Y:Yb")))),
        (1, 'a', List(
           (1, List("X:Xa", "Y:Ya")),
           (1, List("X:Xa", "Y:Yb")),
           (1, List("X:Xb", "Y:Ya")),
           (1, List("X:Xb", "Y:Yb")))),
        (1, 'b', List(
           (1, List("X:Xa", "Y:Ya")),
           (1, List("X:Xa", "Y:Yb")),
           (1, List("X:Xb", "Y:Ya")),
           (1, List("X:Xb", "Y:Yb")))),
        (2, 'a', List(
           (2, List("X:Xa", "Y:Ya")),
           (2, List("X:Xa", "Y:Yb")),
           (2, List("X:Xb", "Y:Ya")),
           (2, List("X:Xb", "Y:Yb")))),
        (2, 'a', List(
           (2, List("X:Xa", "Y:Ya")),
           (2, List("X:Xa", "Y:Yb")),
           (2, List("X:Xb", "Y:Ya")),
           (2, List("X:Xb", "Y:Yb"))))
      ),
      0,
      List((1, "X"), (2, "XY"))
    )

    val simple = NSST(
      Set(0),
      Set('X'),
      List((0, 'a', List((0, List("X:Xa"))))),
      0,
      List((0, "XX"))
    )

    {
      val composed = NSST.composeNssts(simple, n1)
      info(s"Number of states: ${composed.states.size}")
      info(s"Max number of transition destinations: ${maxTransition(composed)}")
      assert(composed.isCopyless)
      assert(composed.transduce("".toList) == Set())
      assert(composed.transduce("a".toList) == Set("aaaa".toList))
    }

    val composed = NSST.composeNssts(n1, n1)
    info(s"Number of states: ${composed.states.size}")
    info(s"Max number of transition destinations: ${maxTransition(composed)}")
    assert(composed.isCopyless)
    assert(composed.transduce("".toList) == Set())
    assert(composed.transduce("a".toList) ==
             Set("a", "b",
                 "aa", "ab", "ba", "bb",
                 "aaaa", "aaab", "aaba", "aabb", "abaa", "abab", "abba", "abbb",
                 "bbbb", "bbba", "bbab", "bbaa", "babb", "baba", "baab", "baaa"
             ).map(_.toList))
  }
}
