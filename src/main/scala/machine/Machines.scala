package com.github.kmn4.expresso.machine

import com.github.kmn4.expresso._
import com.github.kmn4.expresso.math._

/** Nondeterministic monoid SST */
class MSST[Q, A, B, X, Y](
    val states: Set[Q],
    val in: Set[A],
    val xs: Set[X],
    val ys: Set[Y],
    val edges: MSST.Edges[Q, A, B, X, Y],
    val q0: Q,
    val partialF: Map[Q, Set[(Cupstar[X, Update[Y, B]], Cupstar[Y, B])]]
) {
  implicit val updateXMonoid: Monoid[Update[X, Update[Y, B]]] = xs
  implicit val updateYMonoid: Monoid[Update[Y, B]] = ys
  val outF = partialF.withDefaultValue(Set())
  def transOne(q: Q, a: A): Set[(Q, Update[X, Update[Y, B]])] =
    edges.withDefaultValue(Set.empty)((q, a))
  def transition(qs: Set[Q], w: List[A]): Set[(Q, Update[X, Update[Y, B]])] =
    Monoid.transition(qs, w, (q: Q, a: A) => transOne(q, a))
  def outputAt(q: Q, m: Update[X, Update[Y, B]]): Set[List[B]] =
    outF(q).map {
      case (alpha, beta) =>
        val updateY = Monoid.fold(erase1(flatMap1(alpha, m(_))))
        erase1(flatMap1(beta, updateY))
    }
  def transduce(w: List[A]): Set[List[B]] =
    transition(Set(q0), w).flatMap { case (q, m) => outputAt(q, m) }
}

object MSST {
  type Edges[Q, A, B, X, Y] = Map[(Q, A), Set[(Q, Update[X, Update[Y, B]])]]

  type M1[X] = Map[X, List[X]]
  type M2[X, A] = Map[(X, Boolean), List[A]]
  def gamma[X, A](
      xs: Set[X]
  )(
      permutation: M1[X],
      prePost: M2[X, A]
  ): Update[X, A] = {
    val (front, back) = xs
      .map(x =>
        (
          x -> prePost((x, false)).map(Cop2(_)).appended(Cop1(x)),
          x -> (Cop1(x) :: prePost((x, true)).map(Cop2(_)))
        )
      )
      .unzip
    val mid: Update[X, A] = permutation.map { case (x, xs) => x -> xs.map(Cop1(_)) }
    Monoid.fold(List(front.toMap, mid, back.toMap))(xs)
  }

  def proj[X, A](m: Update[X, A]): (M1[X], M2[X, A]) = {
    def aux(x: X, l: List[Cop[X, A]]): M2[X, A] = {
      l.foldRight(List((x, true) -> List[A]())) {
          case (Cop1(x), acc)             => ((x, false) -> Nil) :: acc
          case (Cop2(a), (xb, as) :: acc) => (xb -> (a :: as)) :: acc
          case _                          => throw new Exception("This must not happen")
        }
        .toMap
    }

    (
      m.map { case (x, xas)     => x -> erase2(xas) }.withDefaultValue(Nil),
      m.flatMap { case (x, xas) => aux(x, xas) }.withDefaultValue(Nil)
    )
  }

  def convertMsstToNsst[Q, A, B, X, Y](
      msst: MSST[Q, A, B, X, Y]
  ): NSST[(Q, Map[X, M1[Y]]), A, B, (X, Y, Boolean)] = {
    type S = Map[X, M1[Y]]
    type NQ = (Q, S)
    type Z = (X, Y, Boolean)
    val xs = msst.xs
    val ys = msst.ys
    val zs: Set[Z] = for (x <- xs; y <- ys; b <- List(true, false)) yield (x, y, b)
    implicit val updateYMonoid: Monoid[Update[Y, Cop[Z, B]]] = ys

    def iota(s: S)(x: X): Update[Y, Cop[Z, B]] = {
      val prePost =
        for (y <- ys; b <- List(false, true))
          yield ((y, b) -> (if (b) List((x, y, b))
                            else List((x, y, b))))
      gamma(ys)(s(x), prePost.toMap).view
        .mapValues(_.map { case Cop1(y) => Cop1(y); case Cop2(z) => Cop2(Cop1(z)) })
        .toMap
    }

    def embedUpdate[X, A, B](m: Update[X, B]): Update[X, Cop[A, B]] = {
      m.view
        .mapValues(_.map {
          case Cop1(x) => Cop1(x)
          case Cop2(b) => Cop2(Cop2(b))
        })
        .toMap
    }

    def assignFold(s: S, alpha: Cupstar[X, Update[Y, B]]): Update[Y, Cop[Z, B]] = {
      val iotaS = iota(s) _
      val ms: List[Update[Y, Cop[Z, B]]] = alpha.map {
        case Cop1(x) => iotaS(x)
        case Cop2(m) => embedUpdate(m)
      }
      Monoid.fold(ms)
    }

    def nextState(s: S, mu: Update[X, Update[Y, B]]): (S, Update[Z, B]) = {
      val cache = xs.map(x => x -> proj(assignFold(s, mu(x)))).toMap
      val nextS = cache.map { case (x, (perm, _)) => x -> perm }
      val nextU: Update[Z, B] = zs.map { case (x, y, b) => (x, y, b) -> cache(x)._2(y, b) }.toMap
      (
        nextS,
        nextU
      )
    }

    def nextStates(q: NQ, a: A): Set[(NQ, Update[Z, B])] = q match {
      case (q, s) =>
        msst
          .transOne(q, a)
          .map {
            case (nextQ, mu) => {
              val (nextS, update) = nextState(s, mu)
              ((nextQ, nextS), update)
            }
          }
    }

    val newQ0 = {
      val id = ys.map(y => y -> List(y)).toMap
      val const = xs.map(x => x -> id).toMap
      (msst.q0, const)
    }
    val (newStates, newEdges) = searchStates(Set(newQ0), msst.in)(nextStates)(
      { case (r, _)         => r },
      { case (q, a, (r, m)) => (q, a, m, r) }
    )
    val newOutF: Map[NQ, Set[Cupstar[Z, B]]] = {
      for ((q, s) <- newStates) yield (q, s) -> msst.outF(q).map {
        case (alpha, beta) =>
          val m = assignFold(s, alpha)
          val assigned = beta.flatMap {
            case Cop1(y) => m(y)
            case Cop2(b) => List(Cop2(Cop2(b)))
          }
          erase1(assigned)
      }
    }.toMap

    NSST[NQ, A, B, Z](
      newStates,
      msst.in,
      zs,
      newEdges.toSet,
      newQ0,
      newOutF
    )
  }
}

/** Monoid NFT */
case class MNFT[Q, A, M: Monoid](
    states: Set[Q],
    in: Set[A],
    edges: Set[(Q, A, M, Q)],
    initials: Set[Q],
    partialF: Map[Q, Set[M]]
) {
  val trans = graphToMap(edges) { case (q, a, m, r) => (q, a) -> (r, m) }
  val acceptF = partialF.withDefaultValue(Set.empty)
  def transOne(q: Q, a: A): Set[(Q, M)] = trans((q, a))
  def outputAt(q: Q, m: M): Set[M] = acceptF(q).map(mf => implicitly[Monoid[M]].combine(m, mf))
  def transition(qs: Set[Q], w: List[A]): Set[(Q, M)] = Monoid.transition(qs, w, transOne)
  def transduce(w: List[A]): Set[M] =
    transition(initials, w).flatMap { case (q, m) => outputAt(q, m) }

  /** Returns optimized MNFT.
    *
    * Remove all unreachable states and states from which it cannot transition to
    * any state where output function is non-empty.
    */
  def optimized: MNFT[Q, A, M] = {
    val reachable =
      closure(
        initials,
        graphToMap(edges) { case (q, _, _, r) => q -> r }
      )
    val invReachable =
      closure(partialF.filter { case (q, s) => s.nonEmpty }.keySet, graphToMap(edges) {
        case (q, a, m, r) => r -> q
      })
    val needed = reachable intersect invReachable
    new MNFT[Q, A, M](
      needed,
      in,
      edges.filter { case (q, a, m, r) => needed(q) && needed(r) },
      initials intersect needed,
      acceptF.filter { case (q, _) => needed(q) }
    )
  }

  def toENFT: ENFT[Int, A, M] = {
    trait NQ
    case class OQ(q: Q) extends NQ
    case object Init extends NQ // New initial state
    case object Fin extends NQ // New final state
    val newStates = states.map[NQ](OQ.apply) + Init + Fin
    type Edge = (NQ, Option[A], M, NQ)
    val newEdges = {
      val fromInit = initials.map(q => (Init, None, Monoid[M].unit, OQ(q)))
      val toFinal = for ((q, s) <- acceptF; m <- s) yield (OQ(q), None, m, Fin)
      edges
        .map[Edge] { case (q, a, m, r) => (OQ(q), Some(a), m, OQ(r)) } ++
        toFinal ++ fromInit
    }
    new ENFT[NQ, A, M](newStates, in, newEdges, Init, Fin).renamed
  }

  def unifyInitAndFinal = toENFT
}

/** Monoid NFT with epsilon transition.
  * Inital state and final state of this class Must be singleton.
  */
case class ENFT[Q, A, M: Monoid](
    val states: Set[Q],
    val in: Set[A],
    val edges: Set[(Q, Option[A], M, Q)],
    val initial: Q,
    val finalState: Q
) {
  val trans = graphToMap(edges) { case (q, a, m, r) => (q, a) -> (r, m) }
  def renamed: ENFT[Int, A, M] = {
    val stateMap = (states zip LazyList.from(0)).toMap
    val newEdges = edges.map { case (q, a, m, r) => (stateMap(q), a, m, stateMap(r)) }
    new ENFT(
      stateMap.map(_._2).toSet,
      in,
      newEdges,
      stateMap(initial),
      stateMap(finalState)
    )
  }

  /** Returns an input by which the machine cat output `wanted`.
    * If configuration has `m` of `M` and `prune(m)` is `true`,
    * then that search branch is teminated. */
  def takeInputFor(wanted: M, prune: M => Boolean): List[A] = {
    val inSetEps = List.from(in.map(Option.apply) + None)
    val queue = collection.mutable.Queue[(Q, List[A], M)]((initial, Nil, Monoid[M].unit))
    var visited: Set[(Q, M)] = queue.view.map { case (q, _, m) => (q, m) }.toSet
    def terminate(q: Q, m: M): Boolean = prune(m) || visited((q, m))
    while (queue.nonEmpty) {
      val (q, as1, m1) = queue.dequeue()
      if (q == finalState && m1 == wanted) return as1.reverse
      val added = {
        inSetEps.flatMap(o =>
          trans((q, o)).flatMap {
            case (q, m2) => {
              val as = o match {
                case None    => as1
                case Some(a) => a :: as1
              }
              val m = Monoid[M].combine(m1, m2)
              if (terminate(q, m)) Set.empty
              else Set((q, as, m))
            }
          }
        )
      }
      for ((q, _, m) <- added) visited += ((q, m))
      queue ++= added
    }
    throw new Exception("No input string gives wanted thing.")
  }
}

class DFA[Q, A](
    val states: Set[Q],
    val alpha: Set[A],
    val transition: Map[(Q, A), Q],
    val q0: Q,
    val finalStates: Set[Q]
) {

  def trans(q: Q, w: List[A]): Q =
    w match {
      case Nil    => q
      case a :: w => trans(transition(q, a), w)
    }

  def accept(w: List[A]): Boolean =
    try finalStates.contains(trans(q0, w))
    catch {
      case e: NoSuchElementException => false
    }

  lazy val edges: Set[(Q, A, Q)] = for {
    q <- states
    a <- alpha
    r <- transition.get((q, a))
  } yield (q, a, r)

  def reversed: DFA[Int, A] = {
    val revMap = graphToMap(edges) { case (q, a, r) => (r, a) -> q }
    val (newStates, newEdges) = searchStates(Set(finalStates), alpha) {
      case (qs, a) =>
        val rs = qs.flatMap(q => revMap((q, a)))
        Iterable(rs)
    }(identity, { case (qs, a, rs) => (qs, a, rs) })
    val newEdgeMap =
      newEdges.iterator.map { case (q, a, r) => (q, a) -> r }.toMap[(Set[Q], A), Set[Q]]
    new DFA(
      newStates,
      alpha,
      newEdgeMap,
      finalStates,
      newStates.filter(_ contains q0)
    ).renamed
  }

  def minimized: DFA[Int, A] = reversed.reversed

  def asNFA: NFA[Q, A] = new NFA(
    states,
    alpha,
    transition.map({ case ((p, a), q) => ((p, Some(a)), Set(q)) }).toMap,
    q0,
    finalStates
  )

  def renamed: DFA[Int, A] = {
    val stateMap = (states zip LazyList.from(0)).toMap
    new DFA(
      stateMap.values.toSet,
      alpha,
      transition.map { case ((p, a), q) => (stateMap(p), a) -> stateMap(q) }.toMap,
      stateMap(q0),
      finalStates.map(stateMap)
    )
  }

  def intersect[R](other: DFA[R, A]): DFA[(Q, R), A] = {
    val newStates = for (p <- this.states; q <- other.states) yield (p, q)

    //    val newAlpha = this.alpha union other.alpha
    if (this.alpha != other.alpha)
      throw new java.lang.Exception("Alphabet sets must be same")
    new DFA(
      newStates,
      alpha,
      Map.from(for ((p, q) <- newStates; a <- alpha) yield {
        val k = ((p, q), a)
        val v = (this.transition((p, a)), other.transition((q, a)))
        (k, v)
      }),
      (this.q0, other.q0),
      for (p <- this.finalStates; q <- other.finalStates) yield (p, q)
    )
  }

  def complement: DFA[Q, A] =
    new DFA(states, alpha, transition, q0, states -- finalStates)

  def union[R](other: DFA[R, A]): DFA[(Q, R), A] =
    (this.complement intersect other.complement).complement

  def isEmpty: Boolean = {
    val next = {
      var res: Map[Q, Set[Q]] = Map().withDefaultValue(Set())
      for (((p, _), q) <- transition) res += (p -> (res(p) + q))
      res
    }
    var reachable: Set[Q] = Set(q0)
    var stack: List[Q] = List(q0)
    while (stack.nonEmpty) {
      val p = stack.head
      stack = stack.tail
      val s = next(p)
      stack ++:= (s -- reachable).toList
      reachable ++= s
    }
    (reachable & finalStates).isEmpty
  }

  def symdiff[R](other: DFA[R, A]): DFA[((Q, R), (Q, R)), A] =
    (this intersect other.complement) union (this.complement intersect other)

  def equiv(other: DFA[Q, A]): Boolean = (this symdiff other).isEmpty

  def toParikhAutomaton[L, I]: ParikhAutomaton[Q, A, L, I] = ParikhAutomaton(
    states,
    alpha,
    Set.empty,
    Set.empty,
    transition.map { case ((q, a), r) => (q, a, Map.empty[L, Int], r) }.toSet,
    q0,
    finalStates.map((_, Map.empty)),
    Seq.empty
  )

  def toIdentityNSST: NSST[Q, A, A, Unit] = NSST(
    states,
    alpha,
    Set(()),
    transition.map { case ((q, a), r) => (q, a, Map(() -> List(Cop1(()), Cop2(a))), r) }.toSet,
    q0,
    finalStates.map(q => q -> Set(List[Cop[Unit, A]](Cop1(())))).toMap
  )
}

object DFA {
  def universal[Q, A](q: Q, inSet: Set[A]): DFA[Q, A] = new DFA(
    Set(q),
    inSet,
    inSet.map((q, _) -> q).toMap,
    q,
    Set(q)
  )
}

class NFA[Q, A](
    val states: Set[Q],
    val alpha: Set[A],
    t: Map[(Q, Option[A]), Set[Q]], // εをNoneで表現
    val q0: Q,
    val finalStates: Set[Q]
) {

  val transition: Map[(Q, Option[A]), Set[Q]] = t.withDefaultValue(Set())
  // キーに対して値が定義されていないときに空集合を返す

  def eclosure(aQs: Set[Q]): Set[Q] = {
    var qs = Set[Q]()
    var newQs = aQs
    while (newQs != qs) {
      qs = newQs
      for (q <- qs) newQs = newQs ++ transition((q, None))
    }
    qs
  }

  def transSet(qs: Set[Q], w: List[A]): Set[Q] =
    w match {
      case Nil => eclosure(qs)
      case a :: w =>
        transSet(eclosure(qs).flatMap(q => transition((q, Some(a)))), w)
    }

  def trans(q: Q, w: List[A]): Set[Q] = transSet(Set(q), w)

  def accept(w: List[A]): Boolean =
    (trans(q0, w) & finalStates).nonEmpty

  def toDFA: DFA[Set[Q], A] = {
    val q0DFA = eclosure(Set(q0))
    var statesDFA = Set(q0DFA)
    var u = List(q0DFA) // リストをスタックとして使用
    var transitionDFA = Map[(Set[Q], A), Set[Q]]()

    while (u.nonEmpty) {
      val s = u.head
      u = u.tail
      for (a <- alpha) {
        val t = eclosure(s.flatMap(q => transition((q, Some(a)))))
        transitionDFA += (s, a) -> t
        if (!statesDFA.contains(t)) {
          u = t :: u
          statesDFA += t
        }
      }
    }
    val finalStatesDFA = statesDFA.filter(qs => (qs & finalStates).nonEmpty)

    new DFA(statesDFA, alpha, transitionDFA, q0DFA, finalStatesDFA)
  }
}

case class ParikhAutomaton[Q, A, L, I](
    states: Set[Q],
    inSet: Set[A],
    ls: Set[L],
    is: Set[I],
    edges: Set[(Q, A, ParikhSST.ParikhUpdate[L], Q)],
    q0: Q,
    acceptRelation: Set[(Q, Map[L, Int])],
    acceptFormulas: Seq[Presburger.Formula[Either[I, L]]]
) {
  val trans = graphToMap(edges) { case (q, a, v, r)         => (q, a) -> (r, v) }
  val acceptFunc = graphToMap(acceptRelation) { case (q, v) => q -> v }

  def intersect[R, K](that: ParikhAutomaton[R, A, K, I]): ParikhAutomaton[(Q, R), A, Cop[L, K], I] = {
    type FS = Seq[Presburger.Formula[Either[I, Cop[L, K]]]]
    val newQ0 = (q0, that.q0)
    def vecCoproduct(v: Map[L, Int], u: Map[K, Int]): Map[Cop[L, K], Int] = {
      val lkv = v.map { case (l, n) => Cop1[L, K](l) -> n }
      val lku = u.map { case (k, n) => Cop2[L, K](k) -> n }
      (lkv ++ lku).toMap
    }
    def nextStates(qr: (Q, R), a: A): Set[((Q, R), Map[Cop[L, K], Int])] = {
      val (q, r) = qr
      for {
        (qq, v) <- trans(q, a)
        (rr, u) <- that.trans(r, a)
      } yield ((qq, rr), vecCoproduct(v, u))
    }
    val (newStates, newEdges) = searchStates(Set(newQ0), inSet)(nextStates)(
      _._1,
      { case (qr, a, (qqrr, v)) => (qr, a, v, qqrr) }
    )
    val newAccRel = for {
      (q, r) <- newStates
      v <- acceptFunc(q)
      u <- that.acceptFunc(r)
    } yield ((q, r), vecCoproduct(v, u))
    val newFormulas: FS = {
      val thisFs: FS = acceptFormulas.map(_.renameVars(_.map(Cop1.apply)))
      val thatFs: FS = that.acceptFormulas.map(_.renameVars(_.map(Cop2.apply)))
      thisFs ++ thatFs
    }
    ParikhAutomaton(
      newStates,
      inSet ++ that.inSet,
      ls.map(Cop1.apply) ++ that.ls.map(Cop2.apply),
      is ++ that.is,
      newEdges,
      newQ0,
      newAccRel,
      newFormulas
    )
  }

  /** Returns a pair (n, v) of I vector and L vector that meets the following if exists:
    * there exists w for which this outputs v and formula(n, v) == true. */
  def ilVectorOption: Option[(Map[I, Int], Map[L, Int])] = toParikhSST.ilVectorOption

  def renamed: ParikhAutomaton[Int, A, Int, I] = {
    val qMap = states.zipWithIndex.toMap
    val lMap = ls.zipWithIndex.toMap
    ParikhAutomaton(
      states.map(qMap),
      inSet,
      ls.map(lMap),
      is,
      edges.map { case (q, a, v, r) => (qMap(q), a, v.map { case (l, n) => lMap(l) -> n }, qMap(r)) },
      qMap(q0),
      acceptRelation.map { case (q, v) => (qMap(q), v.map { case (l, n) => lMap(l) -> n }) },
      acceptFormulas.map(_.renameVars(_.map(lMap)))
    )
  }

  def toParikhSST: ParikhSST[Q, A, A, Unit, L, I] = {
    val x = List[Cop[Unit, A]](Cop1(()))
    val update = inSet.map(a => a -> Map(() -> List(Cop1(()), Cop2(a)))).toMap
    ParikhSST(
      states,
      inSet,
      Set(()),
      ls,
      is,
      edges.map { case (q, a, v, r) => (q, a, update(a), v, r) },
      q0,
      acceptRelation.map { case (q, v) => (q, x, v) },
      acceptFormulas
    )
  }

  def ignoreFormulas: NFA[Q, A] = new NFA(
    states,
    inSet,
    graphToMap(edges) { case (q, a, v, r) => (q, Some(a)) -> r },
    q0,
    acceptRelation.map(_._1)
  )
}

object ParikhAutomaton {
  def universal[Q, A, L, I](q: Q, inSet: Set[A]): ParikhAutomaton[Q, A, L, I] =
    DFA.universal(q, inSet).toParikhAutomaton
}
