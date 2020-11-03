package com.github.kmn4.sst

import org.scalatest.flatspec._

object TestRandom {
  import Concepts._
  import scala.util.{Random => R}
  def nextAs[A](as: Seq[A], maxRepeat: Int): List[A] =
    List.fill(R.nextInt(maxRepeat + 1))(as(R.nextInt(as.size)))
  def randomF[X, A](xs: Set[X], as: Set[A], maxRepeatA: Int): Cupstar[X, A] = {
    val useXs: List[X] = R.shuffle(xs.toList).take(R.nextInt(xs.size))
    val aVec = as.toVector
    useXs.foldLeft(nextAs(aVec, maxRepeatA).map[Cop[X, A]](Cop2(_))) {
      case (acc, x) =>
        nextAs(aVec, maxRepeatA).map(Cop2(_)) ++ List(Cop1(x)) ++ acc
    }
  }
  def randomUpdate[X, A](xs: Iterable[X], as: Set[A], maxRepeatA: Int): Update[X, A] = {
    def randomM1X: M1[X] = {
      val xl = xs.toList
      R.shuffle(xl)
        .foldLeft((Map.empty[X, List[X]], R.shuffle(xl))) {
          case ((m, xx), x) => {
            val (took, rst) = xx.splitAt(R.nextInt(xx.length + 1))
            (m + (x -> took), rst)
          }
        }
        ._1
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
    var edges = List.empty[(Q, A, Update[X, B], Q)]
    while (stack nonEmpty) {
      val q = stack.head
      stack = stack.tail
      val fAtQ = for (_ <- 0 until R.nextInt(maxFNum + 1)) yield randomF(vars, out, maxRepeatB)
      outF = outF + (q -> fAtQ.toSet)
      for (a <- in) {
        for (_ <- 0 until R.nextInt(maxTransition + 1)) {
          val r =
            if (states.size < maxStates && R.nextBoolean()) {
              val r = newState()
              states += r
              stack ::= r
              r
            } else {
              R.shuffle(states).head
            }
          edges ::= (q, a, randomUpdate(vars, out, maxRepeatB), r)
        }
      }
    }
    NSST(
      states,
      in,
      vars,
      edges.toSet,
      q0,
      outF
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
    val maxFNum = 2
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
  implicit val logger = NopLogger
  "Construction of MSST" should "be done correctly" in {
    for (_ <- 0 until 100) {
      val n1 = randomNsstCustomized()
      val n2 = randomNsstCustomized()
      val composedTransduction = NSST.composeNsstsToMsst(n1, n2).transduce _
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
      val msst = NSST.composeNsstsToMsst(n1, n2)
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
    for (_ <- 0 until 100) {
      val n1 = randomNsstCustomized()
      val n2 = randomNsstCustomized()
      val composed = n1 compose n2
      assert(composed.isCopyless)
      maxStates = max(maxStates, composed.states.size)
      val composedTransduction = composed.transduce _
      val metaComposed = metaComposition(n1, n2)
      for (_ <- 0 until 10) {
        val w = nextAs(List('a', 'b'), 3)
        if (!(composedTransduction(w) == metaComposed(w))) {
          info(s"${w.mkString} => ${composedTransduction(w)}")
        }
        assert(composedTransduction(w) == metaComposed(w))
      }
    }
    info(s"Maximum state size: ${maxStates}")
  }

  "Presburger formula of randomly generated NSSTs" should
  "be sat iff the domain is nonempty" in {
    import com.microsoft.z3
    val cfg = new java.util.HashMap[String, String]()
    cfg.put("model", "true")
    val out = Seq('a', 'b')
    for (i <- 0 until 100) {
      val n = {
        val in = Set('a', 'b')
        val out = in
        val vars = Set('X', 'Y')
        val maxStates = 10
        val maxFNum = 2
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
      val f = n.presburgerFormula
      val ctx = new z3.Context(cfg)
      val freeVars = out.map(a => s"y$a").map(y => y -> ctx.mkIntConst(y))
      val zero = ctx.mkInt(0)
      val positives = freeVars.map { case (_, v) => ctx.mkGe(v, zero) }
      val expr = Parikh.Formula.formulaToExpr(ctx, freeVars.toMap, f)
      val solver = ctx.mkSolver()
      solver.add(expr +: positives: _*)
      if (solver.check() == z3.Status.SATISFIABLE) {
        assert(!n.isEmpty)
      } else {
        assert(n.isEmpty)
      }
      ctx.close()
    }
  }
}
