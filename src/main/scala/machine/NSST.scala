package com.github.kmn4.sst.machine

import com.github.kmn4.sst._
import com.github.kmn4.sst.math._

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

  def parikhEnft: ENFT[Int, A, Map[B, Int]] = NSST.convertNsstParikhNft(this).unifyInitAndFinal

  /**
    * Generate a Presburger formula that is satisfied by any assignment which represents a Parikh image of
    * an output string of this NSST.
    * Variables representing the number of each output symbol are its `toString` value prefixed with 'y'.
    *
    * @return
    */
  def presburgerFormula: Presburger.Formula[String] = {
    val coutingNft = NSST.convertNsstParikhNft(this)
    val formula = Parikh.parikhEnftToPresburgerFormula(coutingNft.unifyInitAndFinal)
    type E = (Int, Parikh.Image[B], Int)
    type X = Parikh.EnftVar[Int, B, E]
    class Renamer() {
      var i = 0
      private def newVar() = {
        i += 1
        i
      }
      var eMap: Map[E, String] = Map.empty
      var qMap: Map[Int, String] = Map.empty
      def renamer(x: X): String = x match {
        case Parikh.BNum(b)     => s"y${b}"
        case Parikh.EdgeNum(e)  => eMap.getOrElse(e, { val s = s"x${newVar()}"; eMap += e -> s; s })
        case Parikh.Distance(q) => qMap.getOrElse(q, { val s = s"x${newVar()}"; qMap += q -> s; s })
      }
    }
    Presburger.Formula.renameVars(formula)(new Renamer().renamer _)
  }

  /** Returns an input string that give some output.
    * If this NSST is empty, then exception will be thrown.
    */
  def takeInput: List[A] = {
    transitionSystemBFS[Q, A](
      states,
      in, {
        val m = graphToMap(edges) { case (q, a, m, r) => (q, a) -> r }
        (q, a) => m((q, a))
      },
      q0,
      outF.filter { case (_, s) => s.nonEmpty }.keySet
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

  // Returns SST S' that satisfies the following condition:
  // for all w, S'(w) contains w'b (here b is in bs) iff there exist w' and w'' s.t. S(w) contains w' b w''.
  def sstEndsWith(bs: Set[B]): NSST[(Q, Option[X]), A, B, X] = {
    val newOutF = {
      val graph =
        for {
          (q, xbs) <- outGraph
          i <- 0 until xbs.length
        } yield xbs(i) match {
          case Cop1(x)          => Some(((q, Some(x)), xbs.take(i + 1)))
          case Cop2(b) if bs(b) => Some((q, None), xbs.take(i + 1))
          case _                => None
        }
      graphToMap(graph.flatten)(identity)
    }
    type NQ = (Q, Option[X])
    val backTrans = graphToMap(edges) { case (q, a, m, r) => (r, a) -> (q, m) }
    def prevStates(nq: NQ, a: A): Iterable[(NQ, Update[X, B])] = {
      // q -[a / m]-> r
      val (r, x) = nq
      x match {
        case Some(x) => {
          // If q -[a / m]-> r and m(x) = u y v, then
          // (q, y) -[a / m[x mapsto u y]]-> (r, x)
          val assignY =
            for {
              (q, m) <- backTrans((r, a))
              (y, uy) <- {
                val mx = m(x)
                mx.zipWithIndex.flatMap {
                  case (Cop1(y), i) => Some((y, mx.take(i + 1)))
                  case _            => None
                }
              }
            } yield ((q, Some(y)), m + (x -> uy))
          // Also, if q -[a / m]-> r and m(x) = u b v and b is in bs,
          // then (q, _) -[a / m[x mapsto u b]]-> (r, x)
          val assignB =
            for {
              (q, m) <- backTrans((r, a))
              ub <- {
                val mx = m(x)
                mx.zipWithIndex.flatMap {
                  case (Cop2(b), i) if bs(b) => Some(mx.take(i + 1))
                  case _                     => None
                }
              }
            } yield ((q, None), m + (x -> ub))
          assignY ++ assignB
        }
        case None => backTrans((r, a)).map { case (q, m) => ((q, None), m) }
      }
    }

    val (newStates, newEdges) = searchStates(newOutF.keySet, in)(prevStates)(
      { case (q, m)         => q },
      { case (r, a, (q, m)) => (q, a, m, r) }
    )
    NSST(newStates, in, variables, newEdges, (q0, None), newOutF)
  }

  /**
    * Returns CA that reads input w$ and outputs integer n s.t.
    * there exists word w' this SST outputs when it reads w and len(w') == n.
    */
  def lengthCA: CounterAutomaton[Option[(Q, Set[X])], Option[A]] = {
    val newOutF: Map[(Q, Set[X]), Set[Int]] = {
      val graph =
        for ((q, vs) <- outF.toList; alpha <- vs) yield (q, varsIn(alpha)) -> alpha.filter(_.is2).length
      graphToMap(graph)(identity)
    }
    val finalStates = newOutF.keySet
    val backTrans = graphToMap(edges) {
      case (q, a, m, r) => {
        val xsn: Map[X, (Set[X], Int)] = m.map {
          case (x, xbs) =>
            x -> xbs.foldLeft[(Set[X], Int)]((Set.empty, 0)) {
              case (acc, Cop1(x)) => acc.copy(_1 = acc._1 + x)
              case (acc, Cop2(b)) => acc.copy(_2 = acc._2 + 1)
            }
        }
        (r, a) -> (q, xsn)
      }
    }
    def prevStates(qx: (Q, Set[X]), a: A): Set[((Q, Set[X]), Int)] = {
      // If q -[a / m]-> r then ∪ vars(m(x)) is one of previous vars
      // and Σ |chars(m(x))| is length to be added
      val (r, xs) = qx
      backTrans((r, a)).map {
        case (q, m) =>
          (
            (q, xs.flatMap(x => m(x)._1)),
            xs.foldLeft(0) { case (acc, x) => acc + m(x)._2 }
          )
      }
    }

    val (newStates, newEdges) = searchStates(finalStates, in)(prevStates)(
      { case (q, _)         => q },
      { case (r, a, (q, n)) => (q, a, n, r) }
    )
    val newQ0s = newStates.filter { case (q, _) => q == q0 }
    type R = Option[(Q, Set[X])]
    CounterAutomaton(
      addNone(newStates.toSet),
      addNone(in), {
        val hoge = newEdges.view
          .map[(R, Option[A], Int, R)] { case (q, a, n, r) => (Some(q), Some(a), n, Some(r)) }
        val fuga = for ((q, s) <- newOutF; n <- s) yield { (Some(q), None, n, None) }
        (hoge ++ fuga).toSet
      },
      wrapSome(newQ0s.toSet),
      Set(None)
    )
  }

  /** Test whether `this` NSST is functional, i.e. for any input there exists at most one output. */
  def isFunctional: Boolean = {
    // this is functional iff in response to any input
    // 1. it does not output two strings with different length
    // 2. for each pair of diffrent input chars, say a and b,
    //    it does not output two strings that ends with a and b with same length.

    // First decide if 1 holds.
    val ca = lengthCA
    if ((ca diffCM ca) isNonZeroReachable) return false

    // And next, check if 2 holds.
    val outSet = {
      edges.flatMap { case (_, _, m, _) => charsIn(m) } ++
        outF.flatMap { case (_, s)      => s.flatMap(xbs => charsIn(xbs)) }
    }
    val idxAlphabet = outSet.toList.zipWithIndex
    val n = LazyList.from(0).find(1 << _ >= in.size).get
    val partitions =
      (0 until n).map(sh => idxAlphabet partition { case (a, i) => ((1 << sh) & i) == 0 }).map {
        case (l1, l2) => (l1.map(_._1).toSet, l2.map(_._1).toSet)
      }
    for ((s1, s2) <- partitions) {
      val ends1 = sstEndsWith(s1)
      val ends2 = sstEndsWith(s2)
      if ((ends1.lengthCA diffCM ends2.lengthCA) isZeroReachable) return false
    }
    true
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

  /** Convert the given NSST to a NFT that transduces each input to the Parikh image of the output of the NSST. */
  def convertNsstParikhNft[Q, A, B, X](
      nsst: NSST[Q, A, B, X]
  ): MNFT[(Q, Set[X]), A, Map[B, Int]] = {
    type NQ = (Q, Set[X])
    type V = Map[B, Int]
    def charsVecOf(alpha: Cupstar[X, B]): V = alpha.foldLeft[V](Map.empty.withDefaultValue(0)) {
      case (acc, Cop2(b)) => acc.updated(b, acc(b) + 1)
      case (acc, _)       => acc
    }
    val backTrans = graphToMap(nsst.edges) { case (q, a, m, r) => (r, a) -> (q, m) }
    val vectorMonoid: Monoid[V] = Monoid.vectorMonoid(nsst.out)(Monoid.intAdditiveMonoid)
    def prevStates(nq: NQ, a: A): Set[(NQ, V)] = {
      val (r, p) = nq
      for ((q, m) <- backTrans(r, a)) yield {
        (
          (q, p.flatMap(m andThen varsIn _)),
          Monoid.fold(p.toList.map(m andThen charsVecOf _))(vectorMonoid)
        )
      }
    }
    val outF: Map[NQ, Set[V]] = graphToMap {
      nsst.outGraph.map { case (q, alpha) => (q, varsIn(alpha)) -> charsVecOf(alpha) }
    }(identity)
    val (newStates, newEdges) = searchStates(outF.keySet, nsst.in)(prevStates)(
      { case (q, _)         => q },
      { case (r, a, (q, m)) => (q, a, m, r) }
    )
    new MNFT[NQ, A, V](
      newStates,
      nsst.in,
      newEdges,
      newStates.filter(_._1 == nsst.q0).toSet,
      outF
    )(vectorMonoid).optimized
  }

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
