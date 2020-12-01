package com.github.kmn4.sst

import NSST.graphToMap
import Concepts.{Cupstar, Update}

trait StringIntTransducer[A, B, I] {
  def transduce(w: Seq[A], n: Map[I, Int]): Set[Seq[B]]
}

case class ParikhSST[Q, A, B, X, L, I](
    states: Set[Q],
    inSet: Set[A],
    xs: Set[X],
    ls: Set[L],
    is: Set[I],
    edges: Set[(Q, A, Concepts.Update[X, B], ParikhSST.ParikhUpdate[L], Q)],
    q0: Q,
    outGraph: Set[(Q, Concepts.Cupstar[X, B], Map[L, Int])],
    acceptFormulas: Seq[Presburger.Formula[Either[I, L]]]
) extends StringIntTransducer[A, B, I] {
  type XBS = Cupstar[X, B]
  type LVal = Map[L, Int]
  type UpdateX = Update[X, B]
  type UpdateL = ParikhSST.ParikhUpdate[L]
  type UpdateXL = (UpdateX, UpdateL)
  val trans: Map[(Q, A), Set[(Q, UpdateXL)]] = graphToMap(edges) {
    case (q, a, mx, ml, r) => (q, a) -> (r, (mx, ml))
  }
  val outF: Map[Q, Set[(XBS, LVal)]] = graphToMap(outGraph) { case (q, xbs, lv) => q -> (xbs, lv) }
  val acceptFormula: Presburger.Formula[Either[I, L]] = Presburger.Conj(acceptFormulas.distinct)
  def evalFormula(lVal: Map[L, Int], iVal: Map[I, Int]): Boolean = acceptFormula.eval {
    val l = lVal.map { case (l, n) => Right(l) -> n }
    val i = iVal.map { case (i, n) => Left(i) -> n }
    (l ++ i).toMap
  }

  val sst: NSST[Q, A, B, X] = NSST(
    states,
    inSet,
    xs,
    edges.map { case (q, a, mx, ml, r) => (q, a, mx, r) },
    q0,
    NSST.graphToMap(outGraph) { case (q, xbs, _) => q -> xbs }
  )
  val mxMonoid: Monoid[UpdateX] = Concepts.updateMonoid(xs)
  val mlMonoid: Monoid[UpdateL] = ParikhSST.parikhMonoid(ls)
  val mxlMonoid: Monoid[UpdateXL] = Monoid.productMonoid(mxMonoid, mlMonoid)

  def transduce(w: Seq[A]): Set[List[B]] = sst.transduce(w.toList)
  def transition(qs: Set[Q], w: Seq[A]): Set[(Q, UpdateXL)] =
    Monoid.transition(qs, w.toList, (q: Q, a: A) => trans(q, a))(mxlMonoid)
  def outputAt(q: Q, m: UpdateXL, n: Map[I, Int]): Set[List[B]] = {
    val (mx, ml) = m
    outF(q).flatMap {
      case (xbs, lv) =>
        val lMap = mlMonoid.combine(ml, lv)
        if (evalFormula(lMap, n)) Some(Concepts.erase1(Concepts.flatMap1(xbs, mx)))
        else None
    }
  }
  def transduce(w: Seq[A], n: Map[I, Int]): Set[Seq[B]] = transition(Set(q0), w).flatMap {
    case (q, m) => outputAt(q, m, n)
  }

  def renamed: ParikhSST[Int, A, B, Int, Int, I] = {
    val stateMap = (states.zipWithIndex).toMap
    val xMap = (xs.zipWithIndex).toMap
    val lMap = (ls.zipWithIndex).toMap
    def renameXbs(xbs: XBS): Cupstar[Int, B] = xbs.map(_.map1(xMap))
    def renameLVal(lv: LVal): Map[Int, Int] = lv.map { case (l, n) => lMap(l) -> n }
    val newEdges =
      edges
        .flatMap {
          case (q, a, mx, ml, r) if states.contains(q) && states.contains(r) =>
            Some(
              (
                stateMap(q),
                a,
                mx.map { case (x, xbs) => xMap(x) -> renameXbs(xbs) },
                renameLVal(ml),
                stateMap(r)
              )
            )
          case _ => None
        }
    val newF = outGraph.withFilter { case (q, _, _) => states(q) }.map {
      case (q, xbs, lv) => (stateMap(q), renameXbs(xbs), renameLVal(lv))
    }
    ParikhSST(
      stateMap.map(_._2).toSet,
      inSet,
      xMap.values.toSet,
      lMap.values.toSet,
      is,
      newEdges,
      stateMap(q0),
      newF,
      acceptFormulas.map(_.renameVars(l => l.map(lMap)))
    )
  }

  def endWith(bs: Set[B]): ParikhSST[(Q, Option[X]), A, B, X, L, I] = {
    val newOutGraph = outGraph.flatMap {
      case (q, xbs, v) =>
        xbs.zipWithIndex.flatMap {
          case (Cop1(x), i)          => Some((q, Some(x)), xbs.take(i + 1), v)
          case (Cop2(b), i) if bs(b) => Some((q, None), xbs.take(i + 1), v)
          case _                     => None
        }
    }
    type NQ = (Q, Option[X])
    val backTrans = NSST.graphToMap(edges) { case (q, a, mx, mh, r) => (r, a) -> (q, mx, mh) }
    def prevStates(nq: NQ, a: A): Iterable[(NQ, Update[X, B], ParikhSST.ParikhUpdate[L])] = {
      // q -[a / (mx, mh)]-> r
      val (r, x) = nq
      x match {
        case Some(x) => {
          // If q -[a / (mx, mh)]-> r and mx(x) = u y v, then
          // (q, y) -[a / (m[x mapsto u y], mh)]-> (r, x)
          val assignY =
            for {
              (q, mx, mh) <- backTrans((r, a))
              (y, uy) <- {
                val mxx = mx(x)
                mxx.zipWithIndex.flatMap {
                  case (Cop1(y), i) => Some((y, mxx.take(i + 1)))
                  case _            => None
                }
              }
            } yield ((q, Some(y)), mx + (x -> uy), mh)
          // Also, if q -[a / (mx, mh)]-> r and mx(x) = u b v and b is in bs,
          // then (q, _) -[a / (m[x mapsto u b], mh)]-> (r, x)
          val assignB =
            for {
              (q, mx, mh) <- backTrans(r, a)
              ub <- {
                val mxx = mx(x)
                mxx.zipWithIndex.flatMap {
                  case (Cop2(b), i) if bs(b) => Some(mxx.take(i + 1))
                  case _                     => None
                }
              }
            } yield ((q, None), mx + (x -> ub), mh)
          assignY ++ assignB
        }
        case None => backTrans((r, a)).map { case (q, mx, mh) => ((q, None), mx, mh) }
      }
    }
    val (newStates, newEdges) = Concepts.searchStates(newOutGraph.map(_._1), inSet)(prevStates)(
      { case (q, _, _)           => q },
      { case (r, a, (q, mx, mh)) => (q, a, mx, mh, r) }
    )
    ParikhSST(newStates, inSet, xs, ls, is, newEdges, (q0, None), newOutGraph, acceptFormulas)
  }

  // ParikhAutomaton shares inSet (input alphabet), ls (log variables), is (integer variables),
  // and acceptFormulas with PSST.
  // This ParikhAutomaton has non-standard semantics specialized to decide whether a PSST is functional.
  case class ParikhAutomaton[Q](
      states: Set[Q],
      edges: Set[(Q, A, Int, Map[L, Int], Q)],
      q0: Q,
      finalStates: Set[Q]
  ) {
    val trans = graphToMap(edges) { case (q, a, n, lv, r) => (q, a) -> (n, lv, r) }

    def diff[R](that: ParikhAutomaton[R]): ParikhAutomaton[(Q, R)] = {
      val newQ0 = (q0, that.q0)
      ???
    }
  }

  lazy val nonEmptyVarsAt: Map[Q, Set[X]] = {
    import scala.collection.mutable.{Map => MMap, Set => MSet}
    val res: MMap[Q, MSet[X]] = MMap.empty.withDefault(_ => MSet.empty)
    def charExistsIn(xbs: XBS): Boolean = xbs.exists(_.is2)
    var updated = false
    do {
      updated = false
      for ((q, _, mx, ml, r) <- edges) {
        val charAssignedX = xs.filter(x => charExistsIn(mx(x)))
        val nonEmptyXAssigned = xs.filter(x => Concepts.varsIn(mx(x)).exists(res(q).contains))
        val addX = charAssignedX ++ nonEmptyXAssigned
        val resX = res(r)
        if (!(addX subsetOf resX)) {
          updated = true
          resX.addAll(addX)
          res(r) = resX
        }
      }
    } while (updated)

    Map.from { res.map { case (q, s) => q -> s.toSet } }.withDefaultValue(Set.empty)
  }

  def composeNsstsToMsst[R, C, Y, K](
      n1: ParikhSST[Q, A, B, X, L, I],
      n2: ParikhSST[R, B, C, Y, K, I]
  )(implicit logger: CompositionLogger): MonoidSST[Option[(Q, Map[X, (R, R)])], C, Y, K] = {
    // logger.start(n1, n2)

    type UpdateY = Update[Y, C]
    type UpdateK = ParikhSST.ParikhUpdate[K]
    type UpdateXL = (UpdateX, UpdateL)
    type UpdateYK = (UpdateY, UpdateK)
    type NQ = (Q, Map[X, (R, R)])

    val invTransA: Map[(Q, A), Set[(Q, UpdateXL)]] =
      graphToMap(n1.edges) { case (q, a, mx, ml, r) => (r, a) -> ((q, (mx, ml))) }

    val invTransB: Map[(R, B), Set[(R, UpdateYK)]] =
      graphToMap(n2.edges) { case (q, b, my, mk, r) => (r, b) -> (q, (my, mk)) }

    // Consider product construction of two NSSTs.
    // invTransX(p)(r, x) is a set of state `q`s where q may transition to r by reading
    // a content of x at state p.
    val invTransX: Map[Q, Map[(R, X), Set[R]]] = {
      import scala.collection.mutable.{Map => MMap, Set => MSet}
      // At n1.q0, all x can contain empty string, thus q2 can transition to q2.
      // At other q1s, nothing is known about content of each x, hence empty destination set.
      val res: MMap[(Q, X, R), MSet[R]] =
        MMap.empty.withDefault {
          case (q1, x, q2) => (if (q1 == n1.q0) MSet(q2) else MSet.empty)
        }
      def trans(transX: (R, X) => MSet[R])(q: R, xb: Cop[X, B]): Set[(R, Unit)] =
        xb match {
          case Cop1(x) => Set.from(transX(q, x).map((_, ())))
          case Cop2(b) => n2.trans(q, b).map { case (r, _) => (r, ()) }
        }
      var updated = false
      do {
        updated = false
        // q1 =[???/m]=> r1, q2 =[(m(x)@q1)/???]=> r2 then q2 =[(x@r1)/???]=> r2
        for {
          (q1, _, mx, ml, r1) <- n1.edges
          x <- n1.xs
          q2 <- n2.states
        } {
          val cur = res((r1, x, q2))
          val added = Monoid.transition(Set(q2), mx(x), trans { case (q, y) => res((q1, y, q)) }).map(_._1)
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
    println("invTransX")

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
    type NewUpdateX = Update[X, UpdateYK]
    // For each element (f, xbs) of the returned set, the following holds: q -[xas / xbs]-> r by using f.
    def previousStates(nq: NQ, a: A): Set[(NQ, NewUpdateX, UpdateL)] = {
      val (r, kt) = nq
      invTransA(r, a).flatMap {
        case (q, (mx, ml)) => { // q -[a / m]-> r (first NSST)
          val candidates: List[(X, Set[(Map[X, (R, R)], Cupstar[X, UpdateYK])])] =
            kt.map {
              case (x, (k, t)) =>
                // Variables always empty at state q can be ignored
                val nonEmptyAtQ = n1.nonEmptyVarsAt(q)
                val filtered: Cupstar[X, B] = mx(x).filter {
                  case Cop1(x) => nonEmptyAtQ(x)
                  case _       => true
                }
                x -> possiblePreviousOf(k, t, invTransB, invTransX(q), filtered)
            }.toList
          def aux(
              candidates: List[(X, Set[(Map[X, (R, R)], Cupstar[X, UpdateYK])])]
          ): Set[(Map[X, (R, R)], NewUpdateX)] =
            candidates match {
              case Nil => Set((Map.empty, n1.xs.map(x => x -> Nil).toMap))
              case (x, s) :: tl =>
                for ((kt1, mu) <- aux(tl); (kt2, alpha) <- s) yield ((kt1 ++ kt2), mu + (x -> alpha))
            }
          aux(candidates).map { case (kt, newMx) => ((q, kt), newMx, ml) }
        }
      }
    }

    val outGraph: Set[(NQ, Cupstar[X, UpdateYK], Cupstar[Y, C], Map[L, Int], Map[K, Int])] = {
      for {
        (q1, xbs, lv) <- n1.outGraph
        (q2, s2) <- n2.outF
        (kt, xms) <- {
          val nonEmptyAtQ1 = n1.nonEmptyVarsAt(q1)
          val filtered = xbs.filter { case Cop1(x) => nonEmptyAtQ1(x); case _ => true }
          possiblePreviousOf(n2.q0, q2, invTransB, invTransX(q1), filtered)
        }
        (ycs, kv) <- s2
      } yield ((q1, kt), xms, ycs, lv, kv)
    }

    val (states, edges) = Concepts.searchStates(outGraph.map(_._1), n1.inSet)(previousStates)(
      { case (q, _, _)           => q },
      { case (r, a, (q, mx, ml)) => (q, a, mx, ml, r) }
    )

    val initialStates =
      states.filter { case (q, kt) => q == n1.q0 && kt.forall { case (_, (k, t)) => k == t } }
    // logger.backwardFinished(states, edges, initialStates)
    println("backward")

    // Remove all unreachable states.
    val reachables = Concepts.closure[NQ](initialStates, graphToMap(edges) {
      case (q, _, _, _, r) => q -> r
    })
    // logger.unreachablesRemoved(reachables)
    println("unreachables")

    // Wrap states with Option so initial state be unique.
    type NWQ = Option[NQ]
    val newStates = reachables.map[NWQ](Some.apply) + None
    val newEdges = {
      val wrapped =
        for ((q, a, mx, ml, r) <- edges if reachables(q) && reachables(r))
          yield (Some(q), a, mx, ml, Some(r))
      val fromNone =
        for ((q, a, mx, ml, r) <- edges if initialStates(q))
          yield (None, a, mx, ml, Some(r))
      wrapped ++ fromNone
    }
    val newOutGraph: Set[(NWQ, Cupstar[X, UpdateYK], Cupstar[Y, C], Map[L, Int], Map[K, Int])] = {
      val wrapped =
        for ((q, xms, ycs, lv, kv) <- outGraph if reachables(q)) yield (Some(q), xms, ycs, lv, kv)
      val atNone =
        for ((q, xms, ycs, lv, kv) <- outGraph if initialStates(q)) yield (None, xms, ycs, lv, kv)
      wrapped ++ atNone
    }

    val res = new MonoidSST[NWQ, C, Y, K](
      newStates,
      n2.xs,
      n2.ls,
      n1.is ++ n2.is,
      newEdges.toSet,
      None,
      newOutGraph,
      n1.acceptFormulas.map(_.renameVars(_.map[Cop[L, K]](Cop1.apply))) ++ n2.acceptFormulas.map(
        _.renameVars(_.map[Cop[L, K]](Cop2.apply))
      )
    )
    // logger.msstConstructed(res)
    println("msst")
    res
  }

  def compose[R, C, Y, K](that: ParikhSST[R, B, C, Y, K, I]): ParikhSST[Int, A, C, Int, Int, I] = {

    // End of composeNsstsToMsst

    composeNsstsToMsst(this, that)(NopLogger).toLocallyConstrainedAffineParikhSST.toAffineParikhSST.toParikhSST.renamed
  }

  case class MonoidSST[Q, C, Y, K](
      states: Set[Q],
      // inSet: Set[A],
      // xs: Set[X],
      ys: Set[Y],
      // ls: Set[L],
      ks: Set[K],
      is: Set[I],
      edges: Set[
        (Q, A, Update[X, (Update[Y, C], ParikhSST.ParikhUpdate[K])], ParikhSST.ParikhUpdate[L], Q)
      ],
      q0: Q,
      outGraph: Set[
        (
            Q,
            Cupstar[X, (Update[Y, C], ParikhSST.ParikhUpdate[K])],
            Cupstar[Y, C],
            Map[L, Int],
            Map[K, Int]
        )
      ],
      acceptFormulas: Seq[Presburger.Formula[Either[I, Cop[L, K]]]]
  ) extends StringIntTransducer[A, C, I] {
    type YCS = Cupstar[Y, C]
    type UpdateY = Update[Y, C]
    type UpdateK = ParikhSST.ParikhUpdate[K]
    type UpdateYK = (UpdateY, UpdateK)
    type UpdateX = Update[X, UpdateYK]
    type UpdateXL = (UpdateX, UpdateL)
    val myMonoid: Monoid[UpdateY] = Concepts.updateMonoid(ys)
    val mkMonoid: Monoid[UpdateK] = ParikhSST.parikhMonoid(ks)
    val mykMonoid: Monoid[UpdateYK] = Monoid.productMonoid(myMonoid, mkMonoid)
    val mxMonoid: Monoid[UpdateX] = Concepts.updateMonoid(xs)
    val mxlMonoid: Monoid[UpdateXL] = Monoid.productMonoid(mxMonoid, mlMonoid)
    val trans = graphToMap(edges) { case (q, a, mx, ml, r)        => (q, a) -> (r, (mx, ml)) }
    val outF = graphToMap(outGraph) { case (q, xmms, ycs, lv, kv) => q -> (xmms, ycs, lv, kv) }
    val acceptFormula: Presburger.Formula[Either[I, Cop[L, K]]] =
      Presburger.Conj(acceptFormulas.distinct)
    def evalFormula(lkVal: Map[Cop[L, K], Int], iVal: Map[I, Int]): Boolean = acceptFormula.eval {
      val lk = lkVal.map { case (l, n) => Right(l) -> n }
      val i = iVal.map { case (i, n)   => Left(i) -> n }
      (lk ++ i).toMap
    }
    def transition(qs: Set[Q], w: Seq[A]): Set[(Q, UpdateXL)] =
      Monoid.transition(qs, w, (q: Q, a: A) => trans(q, a))(mxlMonoid)
    def outputAt(q: Q, m: UpdateXL, n: Map[I, Int]): Set[Seq[C]] = {
      val (mx, ml) = m
      outF(q).flatMap {
        case (xmms, ycs, lv, kv) =>
          val mxys = Concepts.erase1(Concepts.flatMap1(xmms, mx))
          val (my, mk) = Monoid.fold(mxys)(mykMonoid)
          val klMap = mlMonoid.combine(ml, lv).map { case (l, n) => Cop1(l) -> n } ++
            mkMonoid.combine(mk, kv).map { case (k, n)           => Cop2(k) -> n }
          if (evalFormula(klMap.toMap, n)) Some(Concepts.erase1(Concepts.flatMap1(ycs, my)))
          else None
      }
    }
    def transduce(w: Seq[A], n: Map[I, Int]): Set[Seq[C]] = transition(Set(q0), w).flatMap {
      case (q, m) => outputAt(q, m, n)
    }
    def toLocallyConstrainedAffineParikhSST
        : LocallyConstrainedAffineParikhSST[(Q, Map[X, Map[Y, List[Y]]]), A, C, (X, Y, Boolean), Cop[
          L,
          (X, K)
        ], I] = {
      require(xs.nonEmpty) // For a technical reason
      import Concepts.{erase1, erase2, updateMonoid}
      import MSST.{gamma, proj}
      type Edges =
        Set[
          (Q, A, Update[X, (Update[Y, C], ParikhSST.ParikhUpdate[K])], ParikhSST.ParikhUpdate[L], Q)
        ]
      type M1Y = Map[Y, List[Y]]
      type M2Y = Map[(Y, Boolean), List[C]]
      type S = Map[X, M1Y]
      type NQ = (Q, S)
      type Z = (X, Y, Boolean)
      type J = Cop[L, (X, K)]

      type ZCS = Cupstar[Z, C]
      type UpdateZ = Update[Z, C]
      type JVal = Map[J, Int]
      type UpdateJ = ParikhSST.AffineUpdate[J]
      // Construct PresburgerSST[NQ, A, C, Z, J, I].
      val zs: Set[Z] = for (x <- xs; y <- ys; b <- List(true, false)) yield (x, y, b)
      val js: Set[J] = ls.map(Cop1.apply) ++ (for (x <- xs; k <- ks) yield (x, k)).map(Cop2.apply)

      def iota(s: S)(x: X): Update[Y, Cop[Z, C]] = {
        val prePost =
          for (y <- ys; b <- List(false, true))
            yield ((y, b) -> (if (b) List((x, y, b))
                              else List((x, y, b))))
        gamma(ys)(s(x), prePost.toMap).view
          .mapValues(_.map { case Cop1(y) => Cop1(y); case Cop2(z) => Cop2(Cop1(z)) })
          .toMap
      }

      def embedUpdate[X, A, C](m: Update[X, C]): Update[X, Cop[A, C]] = {
        m.view
          .mapValues(_.map {
            case Cop1(x) => Cop1(x)
            case Cop2(b) => Cop2(Cop2(b))
          })
          .toMap
      }

      type UpdateK2 = Map[K, (Int, Set[(X, K)])]
      val mk2Monoid: Monoid[UpdateK2] = Monoid.vectorMonoid(ks) // product of (Int, +) and (Set, union)
      val mykMonoidEmbed: Monoid[(Update[Y, Cop[Z, C]], UpdateK2)] =
        Monoid.productMonoid(Concepts.updateMonoid(ys), mk2Monoid)
      // (S, List[X, Update]) has information for construct update of composed machine.
      def assignFold(s: S, alpha: Cupstar[X, UpdateYK]): (Update[Y, Cop[Z, C]], UpdateK2) = {
        val iotaS = iota(s) _
        val ms: List[(Update[Y, Cop[Z, C]], UpdateK2)] = alpha.map {
          case Cop1(x)        => (iotaS(x), ks.map(k => k -> (0, Set((x, k)))).toMap)
          case Cop2((my, mk)) => (embedUpdate(my), mk.map { case (k, i) => k -> (i, Set.empty) })
        }
        Monoid.fold(ms)(mykMonoidEmbed)
      }

      def nextState(s: S, mx: UpdateX, ml: UpdateL): (S, Update[Z, C], UpdateJ) = {
        val cache = xs.map { x =>
          val (my, mk2) = assignFold(s, mx(x))
          val (p1, p2) = proj(my)
          x -> (p1, p2, mk2)
        }.toMap
        val nextS = cache.map { case (x, (perm, _, _)) => x -> perm }
        val mz = zs.map { case (x, y, b) => (x, y, b) -> cache(x)._2(y, b) }.toMap
        val mj = js.map[(J, (Int, Set[J]))] {
          case j @ Cop1(l) => j -> (ml(l), Set(j))
          case j @ Cop2((x, k)) =>
            val (_, _, mk2) = cache(x)
            val (i, s) = mk2(k)
            j -> (i, s.map(Cop2.apply))
        }
        (nextS, mz, mj.toMap)
      }

      def nextStates(q: NQ, a: A): Set[(NQ, UpdateZ, UpdateJ)] = q match {
        case (q, s) =>
          this
            .trans(q, a)
            .map {
              case (nextQ, (mx, ml)) => {
                val (nextS, mz, mj) = nextState(s, mx, ml)
                ((nextQ, nextS), mz, mj)
              }
            }
      }

      val newQ0 = {
        val id = ys.map(y => y -> List(y)).toMap
        val const = xs.map(x => x -> id).toMap
        (q0, const)
      }
      val (newStates, newEdges) = Concepts.searchStates(Set(newQ0), inSet)(nextStates)(
        { case (r, _, _)           => r },
        { case (q, a, (r, mz, mj)) => (q, a, mz, mj, r) }
      )
      val newOutGraph: Set[(NQ, ZCS, JVal, Presburger.Formula[Either[I, J]])] = {
        for {
          nq @ (q, s) <- newStates
          (xmms, ycs, lv, kv) <- outF(q)
        } yield {
          val (my, mk) = assignFold(s, xmms)
          val assigned = ycs.flatMap {
            case Cop1(y) => my(y)
            case Cop2(b) => List(Cop2(Cop2(b)))
          }
          val v: Iterable[(J, Int)] = js.map {
            case j @ Cop1(l)      => j -> lv(l)
            case j @ Cop2((x, k)) => j -> 0 // mk(k)._1
          }
          val formula = {
            type FormulaVar = Either[I, Cop[L, (X, K)]]
            val x = xs.head // Here xs should not be empty
            val renamed: Presburger.Formula[FormulaVar] = acceptFormula.renameVars(_.map {
              case Cop1(l) => Cop1(l)
              case Cop2(k) => Cop2((x, k))
            })
            Presburger.Formula.substitute(renamed) {
              case Left(i)        => Presburger.Var(Left(i))
              case Right(Cop1(l)) => Presburger.Var(Right(Cop1(l)))
              case Right(Cop2((_, k))) =>
                val (n, _) = mk(k)
                val consts = Seq(kv(k), n).map(Presburger.Const.apply[FormulaVar])
                Presburger.Add(consts ++ xmms.collect {
                  case Cop1(x) => Presburger.Var[FormulaVar](Right(Cop2((x, k))))
                })
            }
          }
          (nq, erase1(assigned), v.toMap, formula)
        }
      }

      LocallyConstrainedAffineParikhSST(newStates, inSet, zs, js, is, newEdges, newQ0, newOutGraph)
    }
  }

  case class LocallyConstrainedAffineParikhSST[Q, A, B, X, L, I](
      states: Set[Q],
      inSet: Set[A],
      xs: Set[X],
      ls: Set[L],
      is: Set[I],
      edges: Set[(Q, A, Concepts.Update[X, B], ParikhSST.AffineUpdate[L], Q)],
      q0: Q,
      outGraph: Set[(Q, Concepts.Cupstar[X, B], Map[L, Int], Presburger.Formula[Either[I, L]])]
  ) extends StringIntTransducer[A, B, I] {
    type UpdateX = Update[X, B]
    type UpdateL = ParikhSST.AffineUpdate[L]
    type UpdateXL = (UpdateX, UpdateL)
    val mxMonoid: Monoid[UpdateX] = Concepts.updateMonoid(xs)
    val mlMonoid: Monoid[UpdateL] = ParikhSST.affineMonoid(ls)
    val mxlMonoid: Monoid[UpdateXL] = Monoid.productMonoid(mxMonoid, mlMonoid)
    val trans = graphToMap(edges) { case (q, a, mx, ml, r) => (q, a) -> (r, (mx, ml)) }
    val outF = graphToMap(outGraph) { case (q, xbs, lv, f) => q -> (xbs, lv, f) }
    def transition(qs: Set[Q], w: Seq[A]): Set[(Q, UpdateXL)] =
      Monoid.transition(qs, w, (q: Q, a: A) => trans(q, a))(mxlMonoid)
    def outputAt(q: Q, m: UpdateXL, n: Map[I, Int]): Set[Seq[B]] = {
      val (mx, ml) = m
      outF(q).flatMap {
        case (xbs, lv, f) =>
          if (f.eval {
                val lMap = ParikhSST.applyAffine(ml, lv)
                val l = lMap.map { case (l, n) => Right(l) -> n }
                val i = n.map { case (i, n)    => Left(i) -> n }
                (l ++ i).toMap
              }) Some(Concepts.erase1(Concepts.flatMap1(xbs, mx)))
          else None
      }
    }
    def transduce(w: Seq[A], n: Map[I, Int]): Set[Seq[B]] = transition(Set(q0), w).flatMap {
      case (q, m) => outputAt(q, m, n)
    }
    def toAffineParikhSST: AffineParikhSST[Q, A, B, X, Option[L], I] = {
      def embedLv(lv: Map[L, Int], forNone: Int): Map[Option[L], Int] =
        lv.map { case (l, n) => Option(l) -> n } + (None -> forNone)
      def embedMl(ml: ParikhSST.AffineUpdate[L]): ParikhSST.AffineUpdate[Option[L]] =
        ml.map {
          case (l, (n, s)) => Option(l) -> (n, s.map(Option.apply))
        } + (None -> (0, Set()))
      val formulaMap = (for ((_, _, _, f) <- outGraph) yield f).zipWithIndex.toMap
      val newOutGraph = (for ((q, xbs, lv, f) <- outGraph) yield (q, xbs, embedLv(lv, formulaMap(f))))
      val newFormula = Presburger.Disj(formulaMap.map {
        case (f, n) =>
          type NewVar = Either[I, Option[L]]
          val renamed = f.renameVars(_.map(Option.apply))
          Presburger.Conj(
            Seq(Presburger.Eq(Presburger.Var[NewVar](Right(None)), Presburger.Const(n)), renamed)
          )
      }.toSeq)
      val newEdges = edges.map { case (q, a, mx, ml, r) => (q, a, mx, embedMl(ml), r) }
      AffineParikhSST[Q, A, B, X, Option[L], I](
        states,
        inSet,
        xs,
        ls.map(Option.apply) + None,
        is,
        newEdges,
        q0,
        newOutGraph,
        newFormula
      )
    }
  }

  case class AffineParikhSST[Q, A, B, X, L, I](
      states: Set[Q],
      inSet: Set[A],
      xs: Set[X],
      ls: Set[L],
      is: Set[I],
      edges: Set[(Q, A, Concepts.Update[X, B], ParikhSST.AffineUpdate[L], Q)],
      q0: Q,
      outGraph: Set[(Q, Concepts.Cupstar[X, B], Map[L, Int])],
      acceptFormula: Presburger.Formula[Either[I, L]]
  ) extends StringIntTransducer[A, B, I] {
    type XBS = Cupstar[X, B]
    type LVal = Map[L, Int]
    type UpdateX = Update[X, B]
    type UpdateL = ParikhSST.AffineUpdate[L]
    type UpdateXL = (UpdateX, UpdateL)
    val trans: Map[(Q, A), Set[(Q, UpdateXL)]] = graphToMap(edges) {
      case (q, a, mx, ml, r) => (q, a) -> (r, (mx, ml))
    }
    val outF: Map[Q, Set[(XBS, LVal)]] = graphToMap(outGraph) { case (q, xbs, lv) => q -> (xbs, lv) }
    def evalFormula(lVal: Map[L, Int], iVal: Map[I, Int]): Boolean = acceptFormula.eval {
      val l = lVal.map { case (l, n) => Right(l) -> n }
      val i = iVal.map { case (i, n) => Left(i) -> n }
      (l ++ i).toMap
    }

    val mxMonoid: Monoid[UpdateX] = Concepts.updateMonoid(xs)
    val mlMonoid: Monoid[UpdateL] = ParikhSST.affineMonoid(ls)
    val mxlMonoid: Monoid[UpdateXL] = Monoid.productMonoid(mxMonoid, mlMonoid)

    def transition(qs: Set[Q], w: Seq[A]): Set[(Q, UpdateXL)] =
      Monoid.transition(qs, w.toList, (q: Q, a: A) => trans(q, a))(mxlMonoid)
    def outputAt(q: Q, m: UpdateXL, n: Map[I, Int]): Set[List[B]] = {
      val (mx, ml) = m
      outF(q).flatMap {
        case (xbs, lv) =>
          val lMap = ParikhSST.applyAffine(ml, lv)
          if (evalFormula(lMap, n)) Some(Concepts.erase1(Concepts.flatMap1(xbs, mx)))
          else None
      }
    }
    def transduce(w: Seq[A], n: Map[I, Int]): Set[Seq[B]] = transition(Set(q0), w).flatMap {
      case (q, m) => outputAt(q, m, n)
    }
    def toParikhSST: ParikhSST[Option[(Q, Map[L, L])], A, B, X, L, I] = {
      type NQ = (Q, Map[L, L])
      type NewUpdateL = Map[L, Int]
      val newOutGraph = {
        val id = ls.map(l => l -> l).toMap
        outGraph.map { case (q, xbs, lv) => ((q, id), xbs, lv) }
      }
      val backTrans = NSST.graphToMap(edges) { case (q, a, mx, ml, r) => (r, a) -> (q, mx, ml) }
      // ll means Map[L, L], i.e. for each l, where it's going to?
      def llOf(ml: ParikhSST.AffineUpdate[L]): Map[L, L] =
        for ((l2, (_, s)) <- ml; l1 <- s) yield l1 -> l2
      def prevStates(nq: NQ, a: A): Set[(NQ, (UpdateX, NewUpdateL))] = {
        val (r, ll) = nq
        backTrans((r, a)).map {
          case (q, mx, ml) =>
            val llMl = llOf(ml)
            // l is assigned to k and k is to go to j, then l is to go to j.
            val prevLL = for {
              l <- ls
              k <- llMl.get(l)
              j <- ll.get(k)
            } yield l -> j
            val lv = {
              var lv = collection.mutable.Map.from(ls.map(_ -> 0))
              // n is added to l and l is to go to k, then n should be added to k.
              for {
                (l, (n, _)) <- ml
                k <- ll.get(l)
              } lv(k) += n
              lv.toMap
            }
            ((q, prevLL.toMap), (mx, lv))
        }
      }
      val (newStates, newEdges) =
        Concepts.searchStates(newOutGraph.map { case (q, _, _) => q }, inSet)(prevStates)(
          { case (q, _)                => q },
          { case (r, a, (q, (mx, ml))) => (q, a, mx, ml, r) }
        )
      val newQ0 = newStates.filter { case (q, _) => q == q0 }
      val oStates = newStates.map(Option.apply) + None
      val oEdges = {
        val some = newEdges.map { case (q, a, mx, ml, r) => (Option(q), a, mx, ml, Option(r)) }
        val fromNone = for ((q, a, mx, ml, r) <- newEdges if newQ0(q)) yield (None, a, mx, ml, Option(r))
        some ++ fromNone
      }
      val oOutGraph = {
        val some = newOutGraph.map { case (q, mx, ml) => (Option(q), mx, ml) }
        val none = for ((q, mx, ml) <- newOutGraph if newQ0(q)) yield (None, mx, ml)
        some ++ none
      }
      ParikhSST(oStates, inSet, xs, ls, is, oEdges, None, oOutGraph, Seq(acceptFormula))
    }
  }

}

object ParikhSST {
  type ParikhUpdate[L] = Map[L, Int]
  def parikhMonoid[L](ls: Set[L]): Monoid[ParikhUpdate[L]] = Monoid.vectorMonoid(ls)
  type AffineUpdate[L] = Map[L, (Int, Set[L])]
  def affineMonoid[L](ls: Set[L]): Monoid[AffineUpdate[L]] = new Monoid[AffineUpdate[L]] {
    val unit = ls.map(l => l -> (0, Set(l))).toMap
    val mon: Monoid[(Int, Set[L])] = Monoid.productMonoid
    def combine(m1: AffineUpdate[L], m2: AffineUpdate[L]): AffineUpdate[L] = m2.map {
      case (l, (i, s)) =>
        val (j, t) = Monoid.fold(s.map(m1))(mon)
        l -> (i + j, t)
    }
  }
  def applyAffine[L](m: AffineUpdate[L], v: Map[L, Int]): Map[L, Int] = m.map {
    case (l, (i, s)) =>
      l -> (s.map(v).sum + i)
  }

  def substr[A, I](alphabet: Set[A])(iName: I, lName: I): ParikhSST[Int, A, A, Int, Int, I] = {
    import Presburger._
    val X = 0
    type T = Term[Either[I, Int]]
    val i: T = Var(Left(iName))
    val l: T = Var(Left(lName))
    val d: T = Var(Right(0))
    val r0: T = Var(Right(1))
    val r1: T = Var(Right(2))
    val zero: T = Const(0)
    val idxOutOrNegLen = Disj(Seq(Lt(i, zero), Ge(i, d), Le(l, zero)))
    val unit: (Concepts.Update[Int, A], ParikhSST.ParikhUpdate[Int]) =
      (Map(X -> List(Cop1(X))), (1 to 2).map(h => h -> 0).toMap + (0 -> 1))
    val edges = alphabet
      .flatMap { a =>
        val (unitX, unitH) = unit
        val seek = (unitX, unitH + (2 -> 1))
        val take = (Map(X -> List(Cop1(X), Cop2(a))), unitH + (1 -> 1))
        val ignore = unit
        Iterable(
          (0, a, seek, 0),
          (0, a, take, 1),
          (1, a, take, 1),
          (1, a, ignore, 2),
          (2, a, ignore, 2)
        )
      }
      .map { case (q, a, (mx, mh), r) => (q, a, mx, mh, r) }
    ParikhSST[Int, A, A, Int, Int, I](
      Set(0, 1, 2),
      alphabet,
      Set(X),
      Set(0, 1, 2),
      Set(iName, lName),
      edges,
      0,
      (0 to 2).map((_, List(Cop1(X)), (0 to 2).map(h => h -> 0).toMap)).toSet,
      Seq(
        Implies(idxOutOrNegLen, Eq(r0, zero)),
        Implies(Conj(Seq(Not(idxOutOrNegLen), Le(l, Sub(d, i)))), Conj(Seq(Eq(r1, i), Eq(r0, l)))),
        Implies(Conj(Seq(Not(idxOutOrNegLen), Gt(l, Sub(d, i)))), Conj(Seq(Eq(r1, i), Eq(r0, Sub(d, i)))))
      )
    )
  }

  def indexOf[A, I](alphabet: Set[A])(iName: I): ParikhSST[Int, A, A, Int, Int, I] = {
    ???
  }
}
