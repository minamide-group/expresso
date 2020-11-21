package com.github.kmn4.sst

import NSST.graphToMap
import Concepts.{Cupstar, Update}

case class PresburgerSST[Q, A, B, X, L, I](
    states: Set[Q],
    inSet: Set[A],
    xs: Set[X],
    ls: Set[L],
    is: Set[I],
    edges: Set[(Q, A, Concepts.Update[X, B], PresburgerSST.IUpdate[L], Q)],
    q0: Q,
    outGraph: Set[(Q, Concepts.Cupstar[X, B], Map[L, Int])],
    acceptFormulas: Seq[Presburger.Formula[Either[I, L]]]
) {
  type XBS = Cupstar[X, B]
  type LVal = Map[L, Int]
  type UpdateX = Update[X, B]
  type UpdateL = PresburgerSST.IUpdate[L]
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
  val mlMonoid: Monoid[UpdateL] = PresburgerSST.iupdateMonoid(ls)
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
  def transduce(w: Seq[A], n: Map[I, Int]): Set[List[B]] = transition(Set(q0), w).flatMap {
    case (q, m) => outputAt(q, m, n)
  }

  def renamed: PresburgerSST[Int, A, B, Int, Int, I] = {
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
    PresburgerSST(
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

  def endWith(bs: Set[B]): PresburgerSST[(Q, Option[X]), A, B, X, L, I] = {
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
    def prevStates(nq: NQ, a: A): Iterable[(NQ, Update[X, B], PresburgerSST.IUpdate[L])] = {
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
    val newStates = collection.mutable.Set.from(newOutGraph.map(_._1))
    var newEdges: List[(NQ, A, Update[X, B], PresburgerSST.IUpdate[L], NQ)] = Nil
    var stack = newStates.toList
    while (stack.nonEmpty) {
      val h = stack.head
      stack = stack.tail
      for {
        a <- inSet
        (q, mx, mh) <- prevStates(h, a)
      } {
        newEdges ::= (q, a, mx, mh, h)
        if (newStates.add(q)) {
          stack ::= q
        }
      }
    }
    PresburgerSST(newStates.toSet, inSet, xs, ls, is, newEdges.toSet, (q0, None), newOutGraph, acceptFormulas)
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
      n1: PresburgerSST[Q, A, B, X, L, I],
      n2: PresburgerSST[R, B, C, Y, K, I]
  )(implicit logger: CompositionLogger): MonoidSST[Option[(Q, Map[X, (R, R)])], C, Y, K] = {
    // logger.start(n1, n2)

    type UpdateY = Update[Y, C]
    type UpdateK = PresburgerSST.IUpdate[K]
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
      val outF1 = n1.outF.toList
      val outF2 = n2.outF.toList
      for {
        (q1, xbs, lv) <- n1.outGraph
        (q2, s2) <- outF2
        (kt, xms) <- {
          val nonEmptyAtQ1 = n1.nonEmptyVarsAt(q1)
          val filtered = xbs.filter { case Cop1(x) => nonEmptyAtQ1(x); case _ => true }
          possiblePreviousOf(n2.q0, q2, invTransB, invTransX(q1), filtered)
        }
        (ycs, kv) <- s2
      } yield ((q1, kt), xms, ycs, lv, kv)
    }

    var states = outGraph.map(_._1)
    var edges: List[(NQ, A, NewUpdateX, UpdateL, NQ)] = Nil
    var stack: List[NQ] = states.toList
    while (stack.nonEmpty) {
      val r = stack.head
      stack = stack.tail
      for {
        a <- n1.inSet
        (q, mx, ml) <- previousStates(r, a)
      } {
        edges ::= ((q, a, mx, ml, r))
        if (!states.contains(q)) {
          states += q
          stack ::= q
        }
      }
    }

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

  def compose[R, C, Y, K](that: PresburgerSST[R, B, C, Y, K, I]): PresburgerSST[Int, A, C, Int, Int, I] = {

    // End of composeNsstsToMsst

    composeNsstsToMsst(this, that)(NopLogger).toPresburgerSST.renamed
  }

  case class MonoidSST[Q, C, Y, K](
      states: Set[Q],
      // inSet: Set[A],
      // xs: Set[X],
      ys: Set[Y],
      // ls: Set[L],
      ks: Set[K],
      is: Set[I],
      edges: Set[(Q, A, Update[X, (Update[Y, C], PresburgerSST.IUpdate[K])], PresburgerSST.IUpdate[L], Q)],
      q0: Q,
      outGraph: Set[
        (Q, Cupstar[X, (Update[Y, C], PresburgerSST.IUpdate[K])], Cupstar[Y, C], Map[L, Int], Map[K, Int])
      ],
      acceptFormulas: Seq[Presburger.Formula[Either[I, Cop[L, K]]]]
  ) {
    type YCS = Cupstar[Y, C]
    type UpdateY = Update[Y, C]
    type UpdateK = PresburgerSST.IUpdate[K]
    type UpdateYK = (UpdateY, UpdateK)
    type UpdateX = Update[X, UpdateYK]
    type UpdateXL = (UpdateX, UpdateL)
    val myMonoid: Monoid[UpdateY] = Concepts.updateMonoid(ys)
    val mkMonoid: Monoid[UpdateK] = PresburgerSST.iupdateMonoid(ks)
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
    def toPresburgerSST: PresburgerSST[(Q, Map[X, Map[Y, List[Y]]]), A, C, (X, Y, Boolean), Cop[L, K], I] = {
      import Concepts.{erase1, erase2, updateMonoid}
      import MSST.{gamma, proj}
      type Edges =
        Set[(Q, A, Update[X, (Update[Y, C], PresburgerSST.IUpdate[K])], PresburgerSST.IUpdate[L], Q)]
      type M1Y = Map[Y, List[Y]]
      type M2Y = Map[(Y, Boolean), List[C]]
      type S = Map[X, M1Y]
      type NQ = (Q, S)
      type Z = (X, Y, Boolean)
      type J = Cop[L, K]

      type ZCS = Cupstar[Z, C]
      type UpdateZ = Update[Z, C]
      type JVal = Map[J, Int]
      type UpdateJ = PresburgerSST.IUpdate[J]
      // Construct PresburgerSST[NQ, A, C, Z, J, I].
      val zs: Set[Z] = for (x <- xs; y <- ys; b <- List(true, false)) yield (x, y, b)
      val js: Set[J] = ls.map(Cop1.apply) ++ ks.map(Cop2.apply)

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

      val mykMonoidEmbed: Monoid[(Update[Y, Cop[Z, C]], UpdateK)] =
        Monoid.productMonoid(Concepts.updateMonoid(ys), mkMonoid)
      def assignFold(s: S, alpha: Cupstar[X, UpdateYK]): (Update[Y, Cop[Z, C]], UpdateK) = {
        val iotaS = iota(s) _
        val ms: List[(Update[Y, Cop[Z, C]], UpdateK)] = alpha.map {
          case Cop1(x)        => (iotaS(x), mkMonoid.unit)
          case Cop2((my, mk)) => (embedUpdate(my), mk)
        }
        Monoid.fold(ms)(mykMonoidEmbed)
      }

      def nextState(s: S, mu: UpdateX, ml: UpdateL): (S, Update[Z, C], UpdateJ) = {
        val cache = xs
          .map(x =>
            x -> {
              val (my, mk) = assignFold(s, mu(x))
              val (p1, p2) = proj(my)
              (p1, p2, mk)
            }
          )
          .toMap
        val nextS = cache.map { case (x, (perm, _, _)) => x -> perm }
        val mz = zs.map { case (x, y, b) => (x, y, b) -> cache(x)._2(y, b) }.toMap
        val mj = ??? //  <-- This cannot be defined.
        (nextS, mz, mj)
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
      var newStates: Set[NQ] = Set(newQ0)
      var newEdges: List[(NQ, A, UpdateZ, UpdateJ, NQ)] = Nil
      var stack = List(newQ0)
      while (stack.nonEmpty) {
        val q = stack.head
        stack = stack.tail
        for (a <- inSet) {
          val nexts = nextStates(q, a)
          newEdges ++:= nexts.map { case (r, mz, mj) => (q, a, mz, mj, r) }
          val newOnes = nexts.map(_._1) -- newStates
          newStates ++= newOnes
          stack ++:= newOnes.toList
        }
      }
      val newOutGraph: Set[(NQ, ZCS, JVal)] = {
        for {
          nq @ (q, s) <- newStates.toSet
          (xmms, ycs, lv, kv) <- outF(q)
        } yield {
          val (my, mk) = assignFold(s, xmms)
          val assigned = ycs.flatMap {
            case Cop1(y) => my(y)
            case Cop2(b) => List(Cop2(Cop2(b)))
          }
          val v: Iterable[(Cop[L, K], Int)] = lv.map { case (l, n) => Cop1(l) -> n } ++ mkMonoid
            .combine(mk, kv)
            .map {
              case (k, n) => Cop2(k) -> n
            }
          (nq, erase1(assigned), v.toMap)
        }
      }

      PresburgerSST[NQ, A, C, Z, J, I](
        newStates,
        inSet,
        zs,
        js,
        is,
        newEdges.toSet,
        newQ0,
        newOutGraph,
        acceptFormulas
      )
    }
  }

}

object PresburgerSST {
  type IUpdate[L] = Map[L, Int]
  def iupdateMonoid[L](ls: Set[L]): Monoid[IUpdate[L]] = Monoid.vectorMonoid(ls)(Monoid.intAdditiveMonoid)
}
