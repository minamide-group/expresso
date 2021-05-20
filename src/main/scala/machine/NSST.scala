package com.github.kmn4.expresso.machine

import com.github.kmn4.expresso._
import com.github.kmn4.expresso.math._

/** Nondeterministic streaming string transducer */
case class NSST[Q, A, B, X](
    states: Set[Q],
    in: Set[A],
    variables: Set[X],
    edges: Set[(Q, A, Update[X, B], Q)],
    q0: Q,
    partialF: Map[Q, Set[Cupstar[X, B]]]
) {
  import NSST._

  implicit val monoid: Monoid[Update[X, B]] = updateMonoid(variables)
  val outF: Map[Q, Set[Cupstar[X, B]]] = partialF.withDefaultValue(Set())
  val outGraph: List[(Q, Cupstar[X, B])] = mapToGraph(partialF)(identity).toList
  val out: Set[B] = Set.from {
    for {
      (_, _, m, _) <- edges;
      (_, alpha) <- m
      b <- erase1(alpha)
    } yield b
  } ++ Set.from {
    for {
      (q, s) <- outF
      alpha <- s
      b <- erase1(alpha)
    } yield b
  }

  val delta: Map[(Q, A), Set[(Q, Update[X, B])]] =
    graphToMap(edges) { case (q, a, m, r) => (q, a) -> ((r, m)) }

  def transOne(q: Q, a: A): Set[(Q, Update[X, B])] = delta.withDefaultValue(Set.empty)((q, a))
  def transition(qs: Set[Q], w: List[A]): Set[(Q, Update[X, B])] =
    Monoid.transition(qs, w, (q: Q, a: A) => transOne(q, a))
  def outputAt(q: Q, m: Update[X, B]): Set[List[B]] =
    outF(q).map { flatMap1(_, m) }.map(erase1)
  def transduce(w: Seq[A]): Set[List[B]] =
    transition(Set(q0), w.toList).flatMap { case (q, m) => outputAt(q, m) }

  def isCopyless: Boolean = {
    val e = edges.forall { case (_, _, m, _) => isCopylessUpdate(m) }
    val f = outF.forall { case (_, s)        => s.forall(isCopylessOutput(_)) }
    e && f
  }

  def isEmpty: Boolean = {
    val reachables = closure(
      Set(q0),
      graphToMap(edges) { case (q, _, _, r) => q -> r }
    )
    (reachables intersect partialF.filter { case (_, s) => s.nonEmpty }.map(_._1).toSet).isEmpty
  }

  def renamed: NSST[Int, A, B, Int] = {
    val stateMap = (states zip LazyList.from(0)).toMap
    val varMap = (variables zip LazyList.from(0)).toMap
    def renameXbs(xbs: Cupstar[X, B]): Cupstar[Int, B] = xbs.map(_.map1(varMap))
    val newEdges =
      edges
        .flatMap {
          case (q, a, m, r) if states.contains(q) && states.contains(r) =>
            Some((stateMap(q), a, m.map { case (x, xbs) => varMap(x) -> renameXbs(xbs) }, stateMap(r)))
          case _ => None
        }
    val newF = partialF.map { case (q, s) => (stateMap(q), s.map(renameXbs)) }
    NSST(
      stateMap.map(_._2).toSet,
      in,
      varMap.map(_._2).toSet,
      newEdges,
      stateMap(q0),
      newF
    )
  }

  lazy val usedVarsAt: Map[Q, Set[X]] = {
    import scala.collection.mutable.{Map => MMap, Set => MSet}
    val res: MMap[Q, MSet[X]] = MMap
      .from {
        outF.view.mapValues { case s => MSet.from { s.flatMap(varsIn) } }
      }
      .withDefault(_ => MSet.empty)
    var updated = false
    do {
      updated = false
      for ((q, _, m, r) <- edges) {
        val addToQ = res(r).flatMap(x => varsIn(m(x)))
        if (!(addToQ subsetOf res(q))) {
          updated = true
          val atQ = res(q)
          res(q) = atQ ++ addToQ
        }
      }
    } while (updated)

    Map.from { res.map { case (q, s) => q -> Set.from(s) } }.withDefaultValue(Set.empty)
  }
  lazy val nonEmptyVarsAt: Map[Q, Set[X]] = {
    import scala.collection.mutable.{Map => MMap, Set => MSet}
    type XBS = Cupstar[X, B]
    val res: MMap[Q, MSet[X]] = MMap.empty.withDefault(_ => MSet.empty)
    def isCharIn(alpha: XBS): Boolean = alpha.exists {
      case Cop2(_) => true
      case _       => false
    }
    var updated = false
    do {
      updated = false
      for ((q, _, m, r) <- edges) {
        val charAssigned = variables.filter(x => isCharIn(m(x)))
        val nonEmptyVarAssigned = variables.filter(x => varsIn(m(x)).exists(res(q).contains))
        val addToR = charAssigned ++ nonEmptyVarAssigned
        if (!(addToR subsetOf res(r))) {
          updated = true
          val atR = res(r)
          res(r) = atR ++ addToR
        }
      }
    } while (updated)

    Map.from { res.map { case (q, s) => q -> Set.from(s) } }.withDefaultValue(Set.empty)
  }

  /** Returns a NSST with redundant variables removed. */
  def removeRedundantVars: NSST[Q, A, B, X] = {
    type XBS = Cupstar[X, B]
    val newVars = states.flatMap(usedVarsAt) intersect states.flatMap(nonEmptyVarsAt)
    def deleteNotUsed(alpha: XBS): XBS =
      alpha.filter { case Cop1(x) => newVars contains x; case _ => true }
    def newUpdate(m: Update[X, B]): Update[X, B] =
      newVars.map(x => x -> deleteNotUsed(m(x))).toMap
    val newEdges =
      edges.map { case (q, a, m, r) => (q, a, newUpdate(m), r) }
    val newOutF = outF.view
      .mapValues(_.map(deleteNotUsed))
      .toMap
      .filter { case (_, s) => s.nonEmpty }
    NSST(
      states,
      in,
      newVars,
      newEdges,
      q0,
      newOutF
    )
  }

  /** Construct NSST that transduce w to that.transduce(this.transduce(w)). */
  def compose[R, C, Y](that: NSST[R, B, C, Y]): NSST[Int, A, C, Int] = {
    if (!this.isCopyless) {
      throw new Exception(s"Tried to compose NSST, but first NSST was copyfull: ${this.edges}")
    }
    if (!that.isCopyless) {
      throw new Exception(s"Tried to compose NSST, but second NSST was copyfull: ${that.edges}")
    }
    val msst = NSST.composeNsstsToMsst(this, that)
    val nsst = MSST.convertMsstToNsst(msst)
    // logger.nsstConstructed(nsst)
    val res = nsst.renamed.removeRedundantVars
    // logger.redundantVarsRemoved(res)
    res
  }

  def toParikhSST[L, I](ls: Set[L]): ParikhSST[Q, A, B, X, L, I] = ParikhSST(
    states,
    in,
    variables,
    ls,
    Set.empty,
    edges.map { case (q, a, m, r) => (q, a, m, ls.map(_ -> 0).toMap, r) },
    q0,
    outGraph.map { case (q, xbs) => (q, xbs, ls.map(_ -> 0).toMap) }.toSet,
    Seq.empty
  )

  def toParikhSST[L, I]: ParikhSST[Q, A, B, X, L, I] = toParikhSST(Set.empty)
}

object NSST {
  type Edge[Q, A, B, X] = (Q, A, Update[X, B], Q)
  type Edges[Q, A, B, X] = Set[Edge[Q, A, B, X]]
  type Out[Q, X, B] = (Q, Cupstar[X, B])
  def isCopylessUpdate[X, B](update: Update[X, B]): Boolean = {
    val vars = update.keySet
    def count(x: X): Int = update.foldLeft(0) {
      case (acc, (_, rhs)) =>
        acc + rhs.foldLeft(0) {
          case (acc, Cop1(y)) if y == x => acc + 1
          case (acc, _)                 => acc
        }
    }
    vars.forall(count(_) <= 1)
  }
  def isCopylessOutput[X, A](output: Cupstar[X, A]): Boolean = {
    output
      .foldLeft((true, Set[X]())) {
        case ((b, s), Cop1(x)) => (b || s.contains(x), s + x)
        case ((b, s), Cop2(a)) => (b, s)
      }
      ._1
  }

  /**
    * For each element (f, xbs) of the returned set, the following holds: q -[xas / xbs]-> r by using f.
    */
  def possiblePreviousOf[Q, X, A, B](
      q: Q,
      r: Q,
      invTransA: Map[(Q, A), Set[(Q, B)]],
      invTransX: Map[(Q, X), Set[Q]], // For each q2 in invTransX(r2, x), reading x at q2 may lead to r2
      xas: Cupstar[X, A]
  ): Set[(Map[X, (Q, Q)], Cupstar[X, B])] = {
    xas
      .foldRight[Set[(Map[X, (Q, Q)], (Q, Cupstar[X, B]))]](
        Set((Map.empty, (r, Nil))) // accumulates a set of pairs of a mapping and configuration.
      ) {
        case (Cop1(x), acc) =>
          acc.flatMap {
            case (m, (r, xbs)) =>
              invTransX(r, x).map(q => (m + (x -> (q, r)), (q, Cop1(x) :: xbs)))
          }
        case (Cop2(a), acc) =>
          acc.flatMap {
            case (m, (r, xbs)) =>
              invTransA(r, a).map { case (q, b) => (m, (q, Cop2(b) :: xbs)) }
          }
      }
      .withFilter { case (_, (s, _)) => s == q }
      .map { case (m, (_, xbs)) => (m, xbs) }
  }

  def composeNsstsToMsst[Q1, Q2, A, B, C, X, Y](
      n1: NSST[Q1, A, B, X],
      n2: NSST[Q2, B, C, Y]
  ): MSST[Option[(Q1, Map[X, (Q2, Q2)])], A, C, X, Y] = {
    // logger.start(n1, n2)

    type NQ = (Q1, Map[X, (Q2, Q2)])

    val invTransA: Map[(Q1, A), Set[(Q1, Update[X, B])]] =
      graphToMap(n1.edges) { case (q, a, m, r) => (r, a) -> (q, m) }

    val invTransB: Map[(Q2, B), Set[(Q2, Update[Y, C])]] =
      graphToMap(n2.edges) { case (q, b, m, r) => (r, b) -> (q, m) }

    // Consider product construction of two NSSTs.
    // invTransX(p)(r, x) is a set of state `q`s where q may transition to r by reading
    // a content of x at state p.
    val invTransX: Map[Q1, Map[(Q2, X), Set[Q2]]] = {
      import scala.collection.mutable.{Map => MMap, Set => MSet}
      // At n1.q0, all x can contain empty string, thus q2 can transition to q2.
      // At other q1s, nothing is known about content of each x, hence empty destination set.
      val res: MMap[(Q1, X, Q2), MSet[Q2]] =
        MMap.empty.withDefault {
          case (q1, x, q2) => (if (q1 == n1.q0) MSet(q2) else MSet.empty)
        }
      def trans(transX: (Q2, X) => MSet[Q2])(q: Q2, xb: Cop[X, B]): Set[(Q2, Unit)] =
        xb match {
          case Cop1(x) => Set.from(transX(q, x).map((_, ())))
          case Cop2(b) => n2.transOne(q, b).map { case (r, _) => (r, ()) }
        }
      var updated = false
      do {
        updated = false
        // q1 =[???/m]=> r1, q2 =[(m(x)@q1)/???]=> r2 then q2 =[(x@r1)/???]=> r2
        for {
          (q1, _, m, r1) <- n1.edges
          x <- n1.variables
          q2 <- n2.states
        } {
          val cur = res((r1, x, q2))
          val added = Monoid.transition(Set(q2), m(x), trans { case (q, y) => res((q1, y, q)) }).map(_._1)
          if (!(added subsetOf cur)) {
            updated = true
            cur ++= added
          }
          res((r1, x, q2)) = cur
        }
      } while (updated)

      (for (((q1, x, q2), s) <- res; r2 <- s) yield (q1, x, q2, r2))
        .groupMap(_._1) { case (_, x, q2, r2) => (x, q2, r2) }
        .view
        .mapValues(graphToMap(_) { case (x, q2, r2) => (r2, x) -> q2 })
        .toMap
        .withDefaultValue(Map.empty.withDefault { case (q2, _) => Set(q2) })
    }
    // logger.invTransX(invTransX)

    def previousStates(nq: NQ, a: A): Set[(NQ, Update[X, Update[Y, C]])] = {
      val (r, kt) = nq
      invTransA(r, a).flatMap {
        case (q, m) => { // q -[a / m]-> r (first NSST)
          val candidates: List[(X, Set[(Map[X, (Q2, Q2)], Cupstar[X, Update[Y, C]])])] =
            kt.map {
              case (x, (k, t)) =>
                // Variables always empty at state q can be ignored
                val usedAtQ = n1.nonEmptyVarsAt(q)
                val filtered = m(x).filter { case Cop1(x) => usedAtQ contains x; case _ => true }
                x -> possiblePreviousOf(k, t, invTransB, invTransX(q), filtered)
            }.toList
          def aux(
              candidates: List[(X, Set[(Map[X, (Q2, Q2)], Cupstar[X, Update[Y, C]])])]
          ): Set[(Map[X, (Q2, Q2)], Update[X, Update[Y, C]])] =
            candidates match {
              case Nil => Set((Map.empty, n1.variables.map(x => x -> Nil).toMap))
              case (x, s) :: tl =>
                for ((kt1, mu) <- aux(tl); (kt2, alpha) <- s) yield ((kt1 ++ kt2), mu + (x -> alpha))
            }
          aux(candidates).map { case (kt, m) => ((q, kt), m) }
        }
      }
    }

    val outF: Map[NQ, Set[(Cupstar[X, Update[Y, C]], Cupstar[Y, C])]] = {
      val outF1 = n1.outF.toList
      val outF2 = n2.outF.toList
      val graph =
        for {
          (q1, s1) <- outF1
          xbs <- s1
          (q2, s2) <- outF2
          (kt, xms) <- {
            val usedAtQ1 = n1.nonEmptyVarsAt(q1)
            val filtered = xbs.filter { case Cop1(x) => usedAtQ1 contains x; case _ => true }
            possiblePreviousOf(n2.q0, q2, invTransB, invTransX(q1), filtered)
          }
          ycs <- s2
        } yield (q1, kt) -> (xms, ycs)
      graphToMap(graph) { case (k, v) => k -> v }
    }

    val (states, edges) = searchStates(outF.keySet, n1.in)(previousStates)(
      { case (q, m)         => q },
      { case (r, a, (q, m)) => (q, a, m, r) }
    )

    val initialStates =
      states.filter { case (q, kt) => q == n1.q0 && kt.forall { case (_, (k, t)) => k == t } }
    // logger.backwardFinished(states, edges, initialStates)

    // Remove all unreachable states.
    val reachables = closure[NQ](initialStates, graphToMap(edges) { case (q, _, _, r) => q -> r })
    // logger.unreachablesRemoved(reachables)

    // Wrap states with Option so initial state be unique.
    type NWQ = Option[NQ]
    val newStates = reachables.map[NWQ](Some.apply) + None
    val newEdges = {
      val wrapped =
        for ((q, a, m, r) <- edges if reachables(q) && reachables(r))
          yield (Some(q), a, m, Some(r))
      val fromNone =
        for ((q, a, m, r) <- edges if initialStates contains q)
          yield (None, a, m, Some(r))
      wrapped ++ fromNone
    }
    val newOutF: Map[NWQ, Set[(Cupstar[X, Update[Y, C]], Cupstar[Y, C])]] = {
      val wrapped = outF.withFilter { case (q, _) => reachables(q) }.map { case (q, s) => (Some(q): NWQ, s) }
      val atNone = None -> Set.from {
        outF.toList
          .withFilter { case (q, _) => initialStates contains q }
          .flatMap { case (_, s) => s }
      }
      wrapped + atNone
    }

    val res = new MSST[NWQ, A, C, X, Y](
      newStates,
      n1.in,
      n1.variables,
      n2.variables,
      graphToMap(newEdges) { case (q, a, m, r) => (q, a) -> (r, m) },
      None,
      newOutF
    )
    // logger.msstConstructed(res)
    res
  }
  // End of composeNsstsToMsst

  def apply(
      states: Iterable[Int],
      vars: Iterable[Char],
      edges: Iterable[(Int, Char, Iterable[(Int, Iterable[String])])],
      q0: Int,
      outF: Iterable[(Int, String)]
  ): NSST[Int, Char, Char, Char] = {
    def stringToCupstar(s: String): Cupstar[Char, Char] =
      s.map[Cop[Char, Char]] { c => if (c.isUpper) Cop1(c) else Cop2(c) }.toList
    def stringsToUpdate(ss: Iterable[String]): Update[Char, Char] =
      ss.map(s => s.head -> stringToCupstar(s.substring(2))).toMap
    val newEdges =
      edges
        .flatMap { case (q, a, s) => s.map { case (r, m) => (q, a, stringsToUpdate(m), r) } }
    val newF = outF.map { case (q, s) => q -> Set(stringToCupstar(s)) }.toMap
    NSST(
      states.toSet,
      edges.map(_._2).toSet,
      vars.toSet,
      newEdges.toSet,
      q0,
      newF
    )
  }
}
