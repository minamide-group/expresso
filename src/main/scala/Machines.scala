package com.github.kmn4.sst

import scala.collection.immutable.Queue

/**
  * Types and functions relatively independent of concrete machines.
  */
object Concepts {
  type Cupstar[X, B] = List[Cop[X, B]]
  type Update[X, B] = Map[X, Cupstar[X, B]]
  def flatMap1[A, B, C](abs: Cupstar[A, B], f: A => Cupstar[C, B]): Cupstar[C, B] =
    abs.flatMap { case Cop1(a) => f(a); case Cop2(b) => List(Cop2(b)) }
  def erase1[A, B](abs: Cupstar[A, B]): List[B] = abs.flatMap(Cop.erase1(_))
  def erase2[A, B](abs: Cupstar[A, B]): List[A] = abs.flatMap(Cop.erase2(_))
  def varsIn[X, A](xas: Cupstar[X, A]): Set[X] = erase2(xas).toSet
  def charsIn[X, A](xas: Cupstar[X, A]): Set[A] = erase1(xas).toSet
  def charsIn[X, A](m: Update[X, A]): Set[A] = m.flatMap { case (_, xas) => charsIn(xas) }.toSet
  implicit def updateMonoid[X, B](xs: Iterable[X]): Monoid[Update[X, B]] =
    new Monoid[Update[X, B]] {
      def combine(m1: Update[X, B], m2: Update[X, B]): Update[X, B] = Map.from {
        for (x <- xs) yield (x -> flatMap1(m2(x), m1(_)))
      }
      // Some codes assume that updates contain definition for all variables,
      // so cannot use `Map.empty.withDefault(x => x -> List(Cop1(x)))` as `unit`.
      def unit: Update[X, B] = Map.from(xs.map(x => x -> List(Cop1(x))))
    }

  def closure[Q](start: Set[Q], edges: Q => Set[Q]): Set[Q] = {
    def trans(qs: Set[Q]): Set[Q] =
      qs.foldLeft(Set.empty[Q]) { case (acc, q) => acc union edges(q) }
    var newQs = start
    var clos = start
    while (newQs.nonEmpty) {
      newQs = trans(newQs) -- clos
      clos ++= newQs
    }
    clos
  }

  def searchStates[Q, A, C, E](
      baseStates: Set[Q],
      inSet: Set[A]
  )(nextConfigs: (Q, A) => Iterable[C])(toState: C => Q, toEdge: (Q, A, C) => E): (Set[Q], Set[E]) = {
    val states = collection.mutable.Set.from(baseStates)
    var edges: List[E] = Nil
    var stack: List[Q] = states.toList
    while (stack.nonEmpty) {
      val h = stack.head
      stack = stack.tail
      for {
        a <- inSet
        c <- nextConfigs(h, a)
      } {
        edges ::= toEdge(h, a, c)
        val q = toState(c)
        if (states.add(q)) {
          stack ::= q
        }
      }
    }
    (states.toSet, edges.toSet)
  }

  /** Breadth-first search for an input by which given system can transition to final state. */
  def transitionSystemBFS[Q, A](
      states: Set[Q],
      in: Iterable[A],
      trans: (Q, A) => Set[Q],
      q0: Q,
      finals: Set[Q]
  ): List[A] = {
    var visited: Set[Q] = Set.empty
    var toVisit: Queue[(Q, List[A])] = Queue((q0, Nil))
    while (toVisit.nonEmpty) {
      val (q, as) = toVisit.head
      toVisit = toVisit.tail
      if (finals contains q) return as.reverse
      val fromQ = in.flatMap(a => trans(q, a).map((_, a :: as))).toSet
      val notVisited = fromQ.filterNot(visited contains _._1)
      visited ++= notVisited.map(_._1)
      toVisit = toVisit.appendedAll(notVisited)
    }
    throw new Exception("Given system is empty.")
  }
}

/** Nondeterministic streaming string transducer */
case class NSST[Q, A, B, X](
    states: Set[Q],
    in: Set[A],
    variables: Set[X],
    edges: Set[(Q, A, Concepts.Update[X, B], Q)],
    q0: Q,
    partialF: Map[Q, Set[Concepts.Cupstar[X, B]]]
) {
  import NSST._
  import Concepts._

  implicit val monoid: Monoid[Update[X, B]] = variables
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
  def transduce(w: List[A]): Set[List[B]] =
    transition(Set(q0), w).flatMap { case (q, m) => outputAt(q, m) }

  def isCopyless: Boolean = {
    val e = edges.forall { case (_, _, m, _) => isCopylessUpdate(m) }
    val f = outF.forall { case (_, s)        => s.forall(isCopylessOutput(_)) }
    e && f
  }

  def asMonoidNFT: NFT[Q, A, Update[X, B]] = new NFT(
    states,
    in,
    delta.view.mapValues { _.map { case (r, m) => (r, List(m)) } }.toMap,
    q0,
    outF.filter { case (q, s) => s.nonEmpty }.keySet
  )

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
    type Cupstar = Concepts.Cupstar[X, B]
    val res: MMap[Q, MSet[X]] = MMap.empty.withDefault(_ => MSet.empty)
    def isCharIn(alpha: Cupstar): Boolean = alpha.exists {
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
    type Cupstar = Concepts.Cupstar[X, B]
    val newVars = states.flatMap(usedVarsAt) intersect states.flatMap(nonEmptyVarsAt)
    def deleteNotUsed(alpha: Cupstar): Cupstar =
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
        case Parikh.BNum(b) => s"y${b}"
        case Parikh.ENum(e) => eMap.getOrElse(e, { val s = s"x${newVar()}"; eMap += e -> s; s })
        case Parikh.Dist(q) => qMap.getOrElse(q, { val s = s"x${newVar()}"; qMap += q -> s; s })
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
  def compose[R, C, Y](
      that: NSST[R, B, C, Y]
  )(implicit logger: CompositionLogger = NopLogger): NSST[Int, A, C, Int] = {
    if (!this.isCopyless) {
      throw new Exception(s"Tried to compose NSST, but first NSST was copyfull: ${this.edges}")
    }
    if (!that.isCopyless) {
      throw new Exception(s"Tried to compose NSST, but second NSST was copyfull: ${that.edges}")
    }
    val msst = NSST.composeNsstsToMsst(this, that)
    val nsst = MSST.convertMsstToNsst(msst)
    logger.nsstConstructed(nsst)
    val res = nsst.renamed.removeRedundantVars
    logger.redundantVarsRemoved(res)
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

    val (newStates, newEdges) = Concepts.searchStates(newOutF.keySet, in)(prevStates)(
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

    val (newStates, newEdges) = Concepts.searchStates(finalStates, in)(prevStates)(
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
}

object NSST {
  import Concepts._

  def wrapSome[T](s: Set[T]): Set[Option[T]] = s.map[Option[T]](Some.apply)
  def addNone[T](s: Set[T]): Set[Option[T]] = wrapSome(s) + None

  type Edges[Q, A, X, B] = Map[(Q, A), Set[(Q, Update[X, B])]]
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

  def graphToMap[E, K, V](graph: Iterable[E])(f: E => (K, V)): Map[K, Set[V]] =
    graph.view
      .map(f)
      .groupBy(_._1)
      .view
      .mapValues(_.map { case (k, v) => v }.toSet)
      .toMap
      .withDefaultValue(Set.empty)

  def mapToGraph[E, K, V](map: Map[K, Set[V]])(f: ((K, V)) => E): Iterable[E] =
    for ((k, vs) <- map; v <- vs) yield f(k, v)

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
  )(implicit logger: CompositionLogger): MSST[Option[(Q1, Map[X, (Q2, Q2)])], A, C, X, Y] = {
    import Concepts._
    logger.start(n1, n2)

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
    logger.invTransX(invTransX)

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

    val (states, edges) = Concepts.searchStates(outF.keySet, n1.in)(previousStates)(
      { case (q, m)         => q },
      { case (r, a, (q, m)) => (q, a, m, r) }
    )

    val initialStates =
      states.filter { case (q, kt) => q == n1.q0 && kt.forall { case (_, (k, t)) => k == t } }
    logger.backwardFinished(states, edges, initialStates)

    // Remove all unreachable states.
    val reachables = closure[NQ](initialStates, graphToMap(edges) { case (q, _, _, r) => q -> r })
    logger.unreachablesRemoved(reachables)

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
    logger.msstConstructed(res)
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
    val (newStates, newEdges) = Concepts.searchStates(outF.keySet, nsst.in)(prevStates)(
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

/** Nondeterministic monoid SST */
class MSST[Q, A, B, X, Y](
    val states: Set[Q],
    val in: Set[A],
    val xs: Set[X],
    val ys: Set[Y],
    val edges: MSST.Edges[Q, A, B, X, Y],
    val q0: Q,
    val partialF: Map[Q, Set[(Concepts.Cupstar[X, Concepts.Update[Y, B]], Concepts.Cupstar[Y, B])]]
) {
  import Concepts._
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
  import Concepts.{Update, Cupstar, erase1, erase2, updateMonoid}
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
  )(implicit logger: CompositionLogger): NSST[(Q, Map[X, M1[Y]]), A, B, (X, Y, Boolean)] = {
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
    val (newStates, newEdges) = Concepts.searchStates(Set(newQ0), msst.in)(nextStates)(
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

case class CounterAutomaton[Q, A](
    states: Set[Q],
    inSet: Set[A],
    edges: Set[(Q, A, Int, Q)],
    q0s: Set[Q],
    finalStates: Set[Q]
) {
  val trans = NSST.graphToMap(edges) { case (q, a, n, r) => (q, a) -> (r, n) }
  def transduce(w: List[A]): Set[Int] =
    Monoid.transition(q0s, w, (q: Q, a: A) => trans((q, a))).withFilter(qn => finalStates(qn._1)).map(_._2)
  def diffCA[R](that: CounterAutomaton[R, A]): CounterAutomaton[(Q, R), A] = {
    require(inSet == that.inSet)
    val newQ0s = for (q01 <- q0s; q02 <- that.q0s) yield (q01, q02)
    def nexts(qr: (Q, R), a: A): Set[((Q, R), Int)] = {
      val (q, r) = qr
      for {
        (nextQ, n1) <- trans((q, a))
        (nextR, n2) <- that.trans((r, a))
      } yield ((nextQ, nextR), n1 - n2)
    }
    val (newStates, newEdges) = Concepts.searchStates(newQ0s, inSet)(nexts)(
      { case (qr, _)         => qr },
      { case (h, a, (qr, n)) => (h, a, n, qr) }
    )
    CounterAutomaton(
      newStates.toSet,
      inSet,
      newEdges.toSet,
      newQ0s,
      newStates.filter { case (q, r) => finalStates(q) && that.finalStates(r) }.toSet
    )
  }
  def diffCM[R](that: CounterAutomaton[R, A]): CounterMachine[(Q, R)] = {
    val ca = diffCA(that)
    CounterMachine(ca.states, ca.edges.map { case (q, a, n, r) => (q, n, r) }, ca.q0s, ca.finalStates)
  }
}

case class CounterMachine[Q](
    states: Set[Q],
    edges: Set[(Q, Int, Q)],
    q0s: Set[Q],
    finalStates: Set[Q]
) {
  val trans = NSST.graphToMap(edges) { case (q, n, r) => q -> (r, n) }
  def renamed: CounterMachine[Int] = {
    val stateMap = states.zipWithIndex.toMap
    CounterMachine(
      states.map(stateMap),
      edges.withFilter { case (q, _, r) => states(q) && states(r) }.map {
        case (q, n, r) => (stateMap(q), n, stateMap(r))
      },
      q0s.intersect(states).map(stateMap),
      finalStates.intersect(states).map(stateMap)
    )
  }
  def normalized: CounterMachine[(Q, Int)] = {
    val rangeN = edges.foldLeft(Map.from { states.map(q => q -> (0, 0)) }) {
      case (acc, (q, n, _)) => {
        val (min, max) = acc(q)
        acc + (q -> (math.min(min, n), math.max(max, n)))
      }
    }
    val newStates = states.flatMap { q =>
      val (min, max) = rangeN(q)
      (min + 1 to max - 1).map((q, _)) :+ (q, 0)
    }
    val (zeros, nonZeros) = edges partition { case (_, n, _) => n == 0 }
    val (pos, neg) = nonZeros partition { case (_, n, _)     => n > 0 }
    val newEdges = {
      val embedZero = zeros.map { case (q, _, r) => ((q, 0), 0, (r, 0)) }
      val chain = rangeN.toSet[(Q, (Int, Int))].flatMap {
        case (q, (min, max)) =>
          (0 to min + 2 by -1).map(i => ((q, i), -1, (q, i - 1))) ++
            (0 to max - 2).map(i => ((q, i), 1, (q, i + 1)))
      }
      val finishPos = pos.map { case (q, n, r) => ((q, n - 1), 1, (r, 0)) }
      val finishNeg = neg.map { case (q, n, r) => ((q, n + 1), -1, (r, 0)) }
      embedZero ++ chain ++ finishPos ++ finishNeg
    }
    CounterMachine(newStates, newEdges, q0s.map((_, 0)), finalStates.map((_, 0)))
  }
  def isNonZeroReachable: Boolean = {
    sealed trait R
    case class RQ(q: Q) extends R
    case object RPos extends R
    case object RNeg extends R
    val rs = states.map[R](RQ.apply) + RPos + RNeg
    CounterMachine(
      rs,
      edges.map[(R, Int, R)] { case (q, n, r) => (RQ(q), n, RQ(r)) } ++
        finalStates.flatMap(q => List((RQ(q), -1, RPos), (RQ(q), 1, RNeg))) ++
        List((RPos, -1, RPos), (RNeg, 1, RNeg)),
      q0s.map[R](RQ.apply),
      Set[R](RPos, RNeg)
    ).isZeroReachable
  }
  def isZeroReachable: Boolean = normalized.renamed.isZeroReachableNormal
  private def isZeroReachableNormal: Boolean = {
    require(edges.forall { case (_, n, _) => -1 <= n && n <= 1 })
    println(s"Q: ${states.size}, D: ${edges.size}, Q0: ${q0s.size}, Qf: ${finalStates.size}")
    sealed trait G // Stack alphabet
    case object Z extends G // Zero
    case object P extends G // Plus
    case object M extends G // Minus

    // P-automaton, where P is this CM seen as pushdown system (PDS).
    case class NFA[R](states: Set[R], edges: Set[(R, G, R)], finals: Set[R])
    // NFA accepting initial configurations of this PDS i.e. {(q, Z) | q is a initial state}
    type R = Option[Q]
    val initCfg = NFA[R](NSST.addNone(this.states), q0s.map(q => (Some(q), Z, None)), Set(None))

    // NQ: states of new P-automaton that accepts post configurations of initCfg.
    type NQ = Either[R, (Q, List[G], Q)]
    var trans: Set[(Q, G, NQ)] = for ((Some(q), g, r) <- initCfg.edges) yield (q, g, Left(r))
    var postEdges: Set[(NQ, G, NQ)] = Set.empty
    var postStates: Set[NQ] = initCfg.states.map(Left.apply)
    var postFinals: Set[NQ] = initCfg.finals.map(Left.apply)

    val pdsEdges: Set[(Q, List[G], Q)] = edges.flatMap {
      case (q, n, r) => {
          if (n < 0) List(List(Z, M, Z), List(M, M, M), List(P))
          else if (n == 0) List(List(Z, Z), List(M, M), List(P, P))
          else List(List(Z, P, Z), List(M), List(P, P, P))
        }.map(gs => (q, gs, r))
    }

    val pdsEdges0: Map[(Q, G), Set[Q]] = NSST.graphToMap(pdsEdges.flatMap {
      case (q, List(g), r) => Some((q, g) -> r)
      case _               => None
    })(identity)
    val pdsEdges1: Map[(Q, G), Set[(Q, G)]] = NSST.graphToMap(pdsEdges.flatMap {
      case (q, List(g, g1), r) => Some((q, g) -> (r, g1))
      case _                   => None
    })(identity)
    val pdsEdges2: Map[(Q, G), Set[(Q, G, G)]] = NSST.graphToMap(pdsEdges.flatMap {
      case (q, List(g, g1, g2), r) => Some((q, g) -> (r, g1, g2))
      case _                       => None
    })(identity)

    for (r @ (p, List(_, g1, _), p1) <- pdsEdges) {
      postStates += Right(r)
      trans += ((p1, g1, Right(r)))
    }
    var eps: Map[NQ, Set[Q]] = Map.empty.withDefaultValue(Set.empty)
    while (trans.nonEmpty) {
      val t @ (p, g, q) = trans.head
      trans -= t
      val tt = t.copy(_1 = Left(Option(t._1)))
      if (!postEdges(tt)) {
        postEdges += tt
        for (p1 <- pdsEdges0((p, g)) if !eps(q)(p1)) {
          eps += q -> (eps(q) + p1)
          for ((qq, g1, q1) <- postEdges if qq == q) trans += ((p1, g1, q1))
          if (postFinals(q)) postFinals += Left(Option(p1))
        }
        for ((p1, g1) <- pdsEdges1((p, g))) trans += ((p1, g1, q))
        for ((p1, g1, g2) <- pdsEdges2((p, g))) {
          val r = (p, List(g, g1, g2), p1)
          postEdges += ((Right(r), g2, q))
          for (p2 <- eps(Right(r))) trans += ((p2, g2, q))
        }
      }
    }

    val postMap = NSST.graphToMap(postEdges) { case (q, a, r) => (q, Option(a)) -> r }
    finalStates.exists { qf =>
      val nfa = new com.github.kmn4.sst.NFA[NQ, G](
        postStates,
        Set(Z, P, M),
        postMap,
        Left(Option(qf)),
        postFinals
      )
      nfa.accept(List(Z))
    }
  }
}

/** 1-way nondeterministic ε-free transducers a.k.a. NGSM. */
class NFT[Q, A, B](
    val states: Set[Q],
    val in: Set[A],
    val edges: Map[(Q, A), Set[(Q, List[B])]],
    val q0: Q,
    val finals: Set[Q]
) {
  def transOne(q: Q, a: A): Set[(Q, List[B])] = edges.withDefaultValue(Set.empty)((q, a))
  def outputAt(q: Q, bs: List[B]): Set[List[B]] = if (finals contains q) Set(bs) else Set.empty
  def transition(qs: Set[Q], w: List[A]): Set[(Q, List[B])] = Monoid.transition(qs, w, transOne)
  def transduce(w: List[A]): Set[List[B]] =
    transition(Set(q0), w).flatMap { case (q, m) => outputAt(q, m) }
}

object NFT {
  def apply(
      states: Iterable[Int],
      edges: Iterable[(Int, Char, Int, String)],
      q0: Int,
      finals: Set[Int]
  ): NFT[Int, Char, Char] = {
    new NFT(
      states.toSet,
      edges.map(_._2).toSet,
      edges
        .map { case (p, a, q, s) => (p, a) -> (q, s.toList) }
        .groupBy(_._1)
        .map { case (k, v) => k -> v.map(_._2).toSet }
        .toMap,
      q0,
      finals
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
  val trans = NSST.graphToMap(edges) { case (q, a, m, r) => (q, a) -> (r, m) }
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
      Concepts.closure(
        initials,
        NSST.graphToMap(edges) { case (q, _, _, r) => q -> r }
      )
    val invReachable =
      Concepts.closure(partialF.filter { case (q, s) => s.nonEmpty }.keySet, NSST.graphToMap(edges) {
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
class ENFT[Q, A, M: Monoid](
    val states: Set[Q],
    val in: Set[A],
    val edges: Set[(Q, Option[A], M, Q)],
    val initial: Q,
    val finalState: Q
) {
  val trans = NSST.graphToMap(edges) { case (q, a, m, r) => (q, a) -> (r, m) }
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
    val inO = List.from(in.map[Option[A]](Some.apply) + None)
    val monoid = implicitly[Monoid[M]]
    var queue: Queue[(Q, List[A], M)] = Queue((initial, Nil, monoid.unit))
    var visited: Set[(Q, M)] = queue.view.map { case (q, _, m) => (q, m) }.toSet
    def terminate(q: Q, m: M): Boolean = prune(m) || visited((q, m))
    while (queue.nonEmpty) {
      val (q, as1, m1) = queue.head
      queue = queue.tail
      if (q == finalState && m1 == wanted) return as1.reverse
      val added = {
        inO.flatMap(o =>
          trans((q, o)).flatMap {
            case (q, m2) => {
              val as = o match {
                case None    => as1
                case Some(a) => a :: as1
              }
              val m = monoid.combine(m1, m2)
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

  // precondition: transition table must be filled
  def minimized: DFA[Int, A] = {
    def isFinal(p: Q) = finalStates contains p

    def getStates(pair: Set[Q]) = {
      val ls = pair.toList
      if (ls.length == 1) (ls(0), ls(0))
      else (ls(0), ls(1))
    }

    val allPairs = for (p <- states; q <- states) yield Set(p, q)
    var notEquiv = allPairs.filter(pair => {
      val (p, q) = getStates(pair)
      isFinal(p) ^ isFinal(q)
    })
    var save: Set[Set[Q]] = Set()
    while (notEquiv != save) {
      save = notEquiv
      for (pair <- allPairs -- notEquiv) {
        val (p, q) = getStates(pair)
        if (alpha.exists(a => notEquiv contains Set(transition(p, a), transition(q, a)))) {
          notEquiv += pair
        }
      }
    }
    val eqPairs = allPairs -- notEquiv
    var equivs: List[Set[Q]] = List()
    var rest = states

    def eqClass(p: Q): Set[Q] = states.filter(q => eqPairs contains Set(p, q))

    while (rest.nonEmpty) {
      val p = rest.toList.head
      val eqP = eqClass(p)
      equivs ::= eqP
      rest --= eqP
    }
    val newStates = equivs.indices.toSet
    val eq2st: Map[Set[Q], Int] =
      equivs.zipWithIndex.toMap
    val st2eq: Map[Int, Set[Q]] = eq2st.map({ case (s, i) => (i, s) })
    val newTransition: Map[(Int, A), Int] = (for (i <- newStates; a <- alpha) yield {
      val e = st2eq(i)
      val p = e.head
      val d = transition(p, a)
      (i, a) -> eq2st(eqClass(d))
    }).toMap
    new DFA(
      newStates,
      alpha,
      newTransition,
      eq2st(eqClass(q0)),
      finalStates.map(eqClass).map(eq2st)
    )
  }

  def asNFA: NFA[Q, A] = new NFA(
    states,
    alpha,
    transition.map({ case ((p, a), q) => ((p, Some(a)), Set(q)) }).toMap,
    q0,
    finalStates
  )

  def renamed: DFA[Int, A] = {
    var stateMap = (states zip LazyList.from(0)).toMap
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

class RegExp2NFA[A](re: RegExp[A], alphabet: Set[A]) {
  private var state = -1

  private def freshState(): Int = {
    state += 1
    state
  }

  private def setState(i: Int) = state = i

  private def aux(re: RegExp[A]): NFA[Int, A] = re match {
    case EpsExp =>
      val q = freshState()
      new NFA(Set(q), alphabet, Map(), q, Set(q))
    case EmptyExp =>
      val q = freshState()
      new NFA(Set(q), alphabet, Map(), q, Set())
    case DotExp =>
      val q = freshState()
      val r = freshState()
      val trans = alphabet.map[((Int, Option[A]), Set[Int])](a => (q, Some(a)) -> Set(r)).toMap
      new NFA(Set(q, r), alphabet, trans, q, Set(r))
    case CharExp(c) =>
      val s = freshState()
      val t = freshState()
      new NFA(Set(s, t), alphabet, Map((s, Some(c)) -> Set(t)), s, Set(t))
    case OrExp(e1, e2) =>
      val n1 = aux(e1)
      val n2 = aux(e2)
      val s = freshState()
      new NFA(
        n1.states union n2.states union Set(s),
        alphabet,
        n1.transition ++ n2.transition
          ++ Map((s, None) -> Set(n1.q0, n2.q0)),
        s,
        n1.finalStates union n2.finalStates
      )
    case CatExp(e1, e2) =>
      val n1 = aux(e1)
      val n2 = aux(e2)
      new NFA(
        n1.states union n2.states,
        alphabet,
        n1.transition ++ n2.transition
          ++ n1.finalStates.map(q => ((q, None), n1.transition((q, None)) + n2.q0)).toMap,
        n1.q0,
        n2.finalStates
      )
    case StarExp(e) =>
      val n = aux(e)
      val s = freshState()
      new NFA(
        n.states + s,
        alphabet,
        n.transition + ((s, None) -> Set(n.q0))
          ++ n.finalStates.map(q => ((q, None), n.transition((q, None)) + s)).toMap,
        s,
        Set(n.q0)
      )
    case CompExp(e) =>
      val d = aux(e).toDFA.complement.renamed
      val maxState = d.states.max
      setState(maxState + 1)
      d.asNFA
  }

  def construct(): NFA[Int, A] = aux(re)
}
