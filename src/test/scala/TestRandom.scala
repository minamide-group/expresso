package com.github.kmn4.sst

import org.scalatest.flatspec._

object TestRandom {
  import Concepts._
  import scala.util.{Random => R}
  def nextAs[A](as: Seq[A], maxRepeat: Int): List[A] =
    List.fill(R.nextInt(maxRepeat))(as(R.nextInt(as.size)))
  def randomF[X, A](xs: Set[X], as: Set[A], maxRepeatA: Int): Cupstar[X, A] = {
    val useXs: List[X] = R.shuffle(xs.toList).take(R.nextInt(xs.size))
    val aVec = as.toVector
    useXs.foldLeft(nextAs(aVec, maxRepeatA).map[Cop[X, A]](Cop2(_))){ case (acc, x) =>
      nextAs(aVec, maxRepeatA).map(Cop2(_)) ++ List(Cop1(x)) ++ acc }
  }
  def randomUpdate[X, A](xs: Iterable[X], as: Set[A], maxRepeatA: Int): Update[X, A] = {
    def randomM1X: M1[X] = {
      val xl = xs.toList
      R.shuffle(xl)
        .foldLeft((Map.empty[X, List[X]], R.shuffle(xl))) {
          case ((m, xx), x) => {
            val (took, rst) = xx.splitAt(R.nextInt(xx.length+1))
            (m + (x -> took), rst)
          }
      }._1
    }
    def randomM2XA: M2[X, A] = {
      for (x <- xs; b <- List(true, false))
      yield (x, b) -> nextAs(as.toList, maxRepeatA)
    }.toMap
    gamma(xs.toSet)(randomM1X, randomM2XA)
  }
  def randomNSST[Q, A, B, X](
    newState: () => Q,
    in: Set[A],
    out: Set[B],
    vars: Set[X],
    maxStates: Int,
    maxFNum: Int,
    maxRepeatB: Int,
    maxTransition: Int
  ): NSST[Q, A, B, X] = {
    val q0 = newState()
    var states = Set(q0)
    var stack = List(q0)
    var outF = Map.empty[Q, Set[Cupstar[X, B]]]
    var edges = Map.empty[(Q, A), Set[(Q, Update[X, B])]]
    while (stack nonEmpty) {
      val q = stack.head
      stack = stack.tail
      val fAtQ = for (_ <- 0 until R.nextInt(maxFNum)) yield randomF(vars, out, maxRepeatB)
      outF = outF + (q -> fAtQ.toSet)
      for (a <- in) yield {
        var destinations = Set.empty[(Q, Update[X, B])]
        for (_ <- 0 until R.nextInt(maxTransition)) {
          val r =
            if (states.size < maxStates && R.nextBoolean()) {
              val r = newState()
              states += r
              stack ::= r
              r
            } else {
              R.shuffle(states).head
            }
          destinations += ((r, randomUpdate(vars, out, maxRepeatB)))
        }
        edges = edges + ((q, a) -> destinations)
      }
    }
    new NSST(
      states,
      in,
      vars,
      edges,
      q0,
      outF
    )
  }
  def randomNFT[Q, A, B](
    newState: () => Q,
    in: Set[A],
    out: Set[B],
    maxStates: Int,
    maxRepeatB: Int,
    maxTransition: Int
  ): NFT[Q, A, B] = {
    val q0 = newState()
    var states = Set(q0)
    var stack = List(q0)
    var edges = Map.empty[(Q, A), Set[(Q, List[B])]]
    var finals = Set.empty[Q]
    while (stack nonEmpty) {
      val q = stack.head
      stack = stack.tail
      if (R.nextInt(3) != 0) finals += q
      finals += q
      for (a <- in) yield {
        var destinations = Set.empty[(Q, List[B])]
        for (_ <- 0 until R.nextInt(maxTransition)) {
          val r =
            if (states.size < maxStates && R.nextBoolean()) {
              val r = newState()
              states += r
              stack ::= r
              r
            } else {
              R.shuffle(states).head
            }
          destinations += ((r, nextAs(out.toList, maxRepeatB)))
        }
        edges = edges + ((q, a) -> destinations)
      }
    }
    new NFT(
      states,
      in,
      edges,
      q0,
      finals
    )
  }
  def metaComposition[Q1, Q2, A, B, C, X, Y](
    n1: NSST[Q1, A, B, X],
    n2: NSST[Q2, B, C, Y]
  ): List[A] => Set[List[C]] = (w: List[A]) => {
    val out1 = n1.transduce(w)
    out1.flatMap(n2.transduce(_))
  }
  class NextState() {
    var q = 0
    def nextState(): Int = {
      q += 1
      q
    }
  }
  def randomNsstCustomized() = {
    val in = Set('a', 'b')
    val out = in
    val vars = Set('X', 'Y')
    val maxStates = 5
    val maxFNum = 3
    val maxRepeatB = 2
    val maxTransition = 2
    randomNSST(
      new NextState().nextState _,
      in,
      out,
      vars,
      maxStates,
      maxFNum,
      maxRepeatB,
      maxTransition
    )
  }
}

class TestRandom extends AnyFlatSpec {
  import TestRandom._
  "Construction of NSST from NSST and NGSM" should "be done correctly" in {
    for (_ <- 0 until 100) {
      val nsst = randomNsstCustomized()
      val nft = {
        val in = Set('a', 'b')
        val out = in
        val maxStates = 5
        val maxRepeatB = 2
        val maxTransition = 4
        randomNFT(
          new NextState().nextState _,
          in,
          out,
          maxStates,
          maxRepeatB,
          maxTransition
        )
      }
      val composedTransduction = NSST.composeNsstAndNft(nsst, nft).transduce _
      val metaComposed = (w: List[Char]) => {
        val out1 = nsst.transduce(w)
        out1.flatMap(nft.transduce(_))
      }
      for (_ <- 0 until 10) {
        val w = nextAs(List('a', 'b'), 5)
        assert(composedTransduction(w) == metaComposed(w))
      }
    }
  }
  "Construction of MSST" should "be done correctly" in {
    for (_ <- 0 until 100) {
      val n1 = randomNsstCustomized()
      val n2 = randomNsstCustomized()
      val composedTransduction = NSST.composeMSST(n1, n2).transduce _
      val metaComposed = metaComposition(n1, n2)
      for (_ <- 0 until 10) {
        val w = nextAs(List('a', 'b'), 3)
        assert(composedTransduction(w) == metaComposed(w))
      }
    }
  }
  "Conversion of MSST to NSST" should "be done correctly" in {
    for (_ <- 0 until 100) {
      val n1 = randomNsstCustomized()
      val n2 = randomNsstCustomized()
      val msst = NSST.composeMSST(n1, n2)
      val msstTransduction = msst.transduce _
      val nsstTransduction = MSST.convertMsstToNsst(msst).transduce _
      for (_ <- 0 until 10) {
        val w = nextAs(List('a', 'b'), 3)
        assert(msstTransduction(w) == nsstTransduction(w))
      }
    }
  }
  "Composition of randomly generated NSSTs" should "be done correctly" in {
    import scala.math.max
    var maxStates = 0
    for (_ <- 0 until 1000) {
      val n1 = randomNsstCustomized()
      val n2 = randomNsstCustomized()
      val composed = NSST.composeNsstOfNssts(n1, n2)
      assert(composed.isCopyless)
      maxStates = max(maxStates, composed.states.size)
      val composedTransduction = composed.transduce _
      val metaComposed = metaComposition(n1, n2)
      for (_ <- 0 until 10) {
        val w = nextAs(List('a', 'b'), 4)
        assert(composedTransduction(w) == metaComposed(w))
      }
    }
    info(s"Maximum state size: ${maxStates}")
  }

}
