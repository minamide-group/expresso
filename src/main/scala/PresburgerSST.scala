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
        val lMap = PresburgerSST.applyIUpdate(ml, lv)
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
    def renameML(ml: UpdateL): PresburgerSST.IUpdate[Int] = ml.map {
      case (l, (s, n)) =>
        (lMap(l), (s.map(lMap), n))
    }
    val newEdges =
      edges
        .flatMap {
          case (q, a, mx, ml, r) if states.contains(q) && states.contains(r) =>
            Some(
              (
                stateMap(q),
                a,
                mx.map { case (x, xbs) => xMap(x) -> renameXbs(xbs) },
                renameML(ml),
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

  // lazy val usedVarsAt: Map[Q, (Set[X], Set[L])] = {
  //   import scala.collection.mutable.{Map => MMap, Set => MSet}
  //   val res: MMap[Q, MSet[X]] = MMap
  //     .from {
  //       outF.view.mapValues { case s => MSet.from { s.flatMap(Concepts.varsIn) } }
  //     }
  //     .withDefault(_ => MSet.empty)
  //   var updated = false
  //   do {
  //     updated = false
  //     for ((q, _, m, r) <- edges) {
  //       val addToQ = res(r).flatMap(x => varsIn(m(x)))
  //       if (!(addToQ subsetOf res(q))) {
  //         updated = true
  //         val atQ = res(q)
  //         res(q) = atQ ++ addToQ
  //       }
  //     }
  //   } while (updated)

  //   Map.from { res.map { case (q, s) => q -> Set.from(s) } }.withDefaultValue(Set.empty)
  // }
  // TODO
  // def getNonEmpty(): Map[T, Set[S]]
  lazy val nonEmptyVarsAt: Map[Q, (Set[X], Set[L])] = {
    import scala.collection.mutable.{Map => MMap, Set => MSet}
    val res: MMap[Q, (MSet[X], MSet[L])] = MMap.empty.withDefault(_ => (MSet.empty, MSet.empty))
    def charExistsIn(xbs: XBS): Boolean = xbs.exists(_.is2)
    var updated = false
    do {
      updated = false
      for ((q, _, mx, ml, r) <- edges) {
        val charAssignedX = xs.filter(x => charExistsIn(mx(x)))
        val nonZeroAssignedL = ls.filter(l => ml(l)._2 != 0)
        val nonEmptyXAssigned = xs.filter(x => Concepts.varsIn(mx(x)).exists(res(q)._1.contains))
        val nonEmptyLAssigned = ls.filter(l => ml(l)._1.exists(res(q)._2.contains))
        val addX = charAssignedX ++ nonEmptyXAssigned
        val addL = nonZeroAssignedL ++ nonEmptyLAssigned
        val (resX, resL) = res(r)
        if (!(addX subsetOf resX) || !(addL subsetOf resL)) {
          updated = true
          resX.addAll(addX)
          resL.addAll(addL)
          res(r) = (resX, resL)
        }
      }
    } while (updated)

    Map
      .from { res.map { case (q, (x, l)) => q -> (x.toSet, l.toSet) } }
      .withDefaultValue((Set.empty, Set.empty))
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
                val (nonEmptyAtQ, _) = n1.nonEmptyVarsAt(q)
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
          val (nonEmptyAtQ1, _) = n1.nonEmptyVarsAt(q1)
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
          val klMap = PresburgerSST.applyIUpdate(ml, lv).map { case (l, n) => Cop1(l) -> n } ++
            PresburgerSST.applyIUpdate(mk, kv).map { case (k, n)           => Cop2(k) -> n }
          if (evalFormula(klMap.toMap, n)) Some(Concepts.erase1(Concepts.flatMap1(ycs, my)))
          else None
      }
    }
    def transduce(w: Seq[A], n: Map[I, Int]): Set[Seq[C]] = transition(Set(q0), w).flatMap {
      case (q, m) => outputAt(q, m, n)
    }
    def toPresburgerSST
        : PresburgerSST[(Q, Map[X, (Map[Y, List[Y]], Map[K, Set[K]])]), A, C, (X, Y, Boolean), Either[
          L,
          (X, K)
        ], I] = {
      import Concepts.{erase1, erase2, updateMonoid}
      type Edges =
        Set[(Q, A, Update[X, (Update[Y, C], PresburgerSST.IUpdate[K])], PresburgerSST.IUpdate[L], Q)]
      type M1Y = Map[Y, List[Y]]
      type M1K = Map[K, Set[K]]
      type M1 = (M1Y, M1K)
      type M2Y = Map[(Y, Boolean), List[C]]
      type S = Map[X, M1]
      type NQ = (Q, S)
      type Z = (X, Y, Boolean)
      type J = Either[L, (X, K)]
      // Construct PresburgerSST[NQ, A, C, Z, J, I].
      val zs: Set[Z] = for (x <- xs; y <- ys; b <- List(true, false)) yield (x, y, b)
      val js: Set[J] = ls.map(Left.apply) ++ (for (x <- xs; k <- ks) yield Right(x, k))

      def gamma(
          permutation: M1Y,
          prePost: M2Y
      ): Update[Y, A] = {
        val (front, back) = ys
          .map(x =>
            (
              x -> prePost((x, false)).map(Cop2(_)).appended(Cop1(x)),
              x -> (Cop1(x) :: prePost((x, true)).map(Cop2(_)))
            )
          )
          .unzip
        val mid: Update[X, A] = permutation.map { case (x, ys) => x -> ys.map(Cop1(_)) }
        Monoid.fold(List(front.toMap, mid, back.toMap))(ys)
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

      def nextStates(q: NQ, a: A): Set[(NQ, Update[Z, C])] = q match {
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
      var newStates: Set[NQ] = Set(newQ0)
      var newEdges: List[(NQ, A, Update[Z, B], NQ)] = Nil
      var stack = List(newQ0)
      while (stack.nonEmpty) {
        val q = stack.head
        stack = stack.tail
        for (a <- msst.in) {
          val nexts = nextStates(q, a)
          newEdges ++:= nexts.map { case (r, m) => (q, a, m, r) }
          val newOnes = nexts.map(_._1) -- newStates
          newStates ++= newOnes
          stack ++:= newOnes.toList
        }
      }
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

      PresburgerSST[NQ, A, C, Z, J, I](
        newStates,
        inSet,
        zs,
        js,
        is,
        newEdges.toSet,
        newQ0,
        newOutF,
        ??? // <--- This can not be defined.
      )
    }
  }
  // def endWith(bs: Set[B]): PresburgerSST[(Q, Option[X]), A, B, X, H, I] = {
  //   val newOutGraph = outGraph.flatMap {
  //     case (q, xbs, v) =>
  //       xbs.zipWithIndex.flatMap {
  //         case (Cop1(x), i)          => Some((q, Some(x)), xbs.take(i + 1), v)
  //         case (Cop2(b), i) if bs(b) => Some((q, None), xbs.take(i + 1), v)
  //         case _                     => None
  //       }
  //   }
  //   type NQ = (Q, Option[X])
  //   val backTrans = NSST.graphToMap(edges) { case (q, a, mx, mh, r) => (r, a) -> (q, mx, mh) }
  //   def prevStates(nq: NQ, a: A): Iterable[(NQ, Update[X, B], Update[H, Int])] = {
  //     // q -[a / (mx, mh)]-> r
  //     val (r, x) = nq
  //     x match {
  //       case Some(x) => {
  //         // If q -[a / (mx, mh)]-> r and mx(x) = u y v, then
  //         // (q, y) -[a / (m[x mapsto u y], mh)]-> (r, x)
  //         val assignY =
  //           for {
  //             (q, mx, mh) <- backTrans((r, a))
  //             (y, uy) <- {
  //               val mxx = mx(x)
  //               mxx.zipWithIndex.flatMap {
  //                 case (Cop1(y), i) => Some((y, mxx.take(i + 1)))
  //                 case _            => None
  //               }
  //             }
  //           } yield ((q, Some(y)), mx + (x -> uy), mh)
  //         // Also, if q -[a / (mx, mh)]-> r and mx(x) = u b v and b is in bs,
  //         // then (q, _) -[a / (m[x mapsto u b], mh)]-> (r, x)
  //         val assignB =
  //           for {
  //             (q, mx, mh) <- backTrans(r, a)
  //             ub <- {
  //               val mxx = mx(x)
  //               mxx.zipWithIndex.flatMap {
  //                 case (Cop2(b), i) if bs(b) => Some(mxx.take(i + 1))
  //                 case _                     => None
  //               }
  //             }
  //           } yield ((q, None), mx + (x -> ub), mh)
  //         assignY ++ assignB
  //       }
  //       case None => backTrans((r, a)).map { case (q, mx, mh) => ((q, None), mx, mh) }
  //     }
  //   }
  //   val newStates = collection.mutable.Set.from(newOutGraph.map(_._1))
  //   var newEdges: List[(NQ, A, Update[X, B], Update[H, Int], NQ)] = Nil
  //   var stack = newStates.toList
  //   while (stack.nonEmpty) {
  //     val h = stack.head
  //     stack = stack.tail
  //     for {
  //       a <- inSet
  //       (q, mx, mh) <- prevStates(h, a)
  //     } {
  //       newEdges ::= (q, a, mx, mh, h)
  //       if (newStates.add(q)) {
  //         stack ::= q
  //       }
  //     }
  //   }
  //   PresburgerSST(newStates.toSet, inSet, xs, hs, is, newEdges.toSet, (q0, None), newOutGraph, acceptFormula)
  // }

}

object PresburgerSST {
  type IUpdate[L] = Map[L, (Set[L], Int)]
  def iupdateMonoid[L](ls: Set[L]): Monoid[IUpdate[L]] = new Monoid[IUpdate[L]] {
    val unitVal = ls.map(l => l -> (Set(l), 0)).toMap
    val mon: Monoid[(Set[L], Int)] = Monoid.productMonoid(Monoid.setUnionMonoid, Monoid.intAdditiveMonoid)
    def unit: IUpdate[L] = unitVal
    def combine(m1: IUpdate[L], m2: IUpdate[L]): IUpdate[L] =
      ls.map { l =>
        l -> {
          val (s, i) = m2(l)
          s.foldLeft((Set.empty[L], i)) { case (acc, l) => mon.combine(acc, m1(l)) }

        }
      }.toMap
  }
  def applyIUpdate[L](m: IUpdate[L], li: Map[L, Int]): Map[L, Int] =
    li.map { case (l, i) => l -> { val (_, j) = m(l); i + j } }
}
