package com.github.kmn4.sst

import scala.collection.immutable.Queue

/**
  * Types and functions relatively independent of concrete machines.
  */
object Concepts {
  def flatMap1[A, B, C](abs: Cupstar[A, B], f: A => Cupstar[C, B]): Cupstar[C, B] =
    abs.flatMap { case Cop1(a) => f(a); case Cop2(b) => List(Cop2(b)) }
  def erase1[A, B](abs: Cupstar[A, B]): List[B] = abs.flatMap(Cop.erase1(_))
  def erase2[A, B](abs: Cupstar[A, B]): List[A] = abs.flatMap(Cop.erase2(_))
  type Cupstar[X, B] = List[Cop[X, B]]
  type Update[X, B] = Map[X, Cupstar[X, B]]
  implicit def updateMonoid[X, B](xs: Iterable[X]): Monoid[Update[X, B]] =
    new Monoid[Update[X, B]] {
      def combine(m1: Update[X, B], m2: Update[X, B]): Update[X, B] = Map.from {
        for (x <- xs) yield (x -> flatMap1(m2(x), m1(_)))
      }
      // Some codes assume that updates contain definition for all variables,
      // so cannot use `Map.empty.withDefault(x => x -> List(Cop1(x)))` as `unit`.
      def unit: Update[X, B] = Map.from(xs.map(x => x -> List(Cop1(x))))
    }

  def varsIn[X, A](alpha: Cupstar[X, A]): Set[X] = alpha.foldLeft[Set[X]](Set.empty) {
    case (acc, xa) =>
      xa match {
        case Cop1(x) => acc + x
        case Cop2(_) => acc
      }
  }

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
  val out: Set[B] = Set.from {
    for ((_, _, m, _) <- edges;
         (_, alpha) <- m;
         b <- erase1(alpha))
      yield b
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

  /** Returns NSST redundant variables removed.
    */
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
  def presburgerFormula: Parikh.Formula[String] = NSST.parikhImagePresburger(this)

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
  def compose[R, C, Y](that: NSST[R, B, C, Y]): NSST[Int, A, C, Int] =
    NSST.composeNsstsToNsst(this, that).renamed.removeRedundantVars
}

object NSST {
  import Concepts._
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

  /** Returns a set of `Map`s that maps each variable y in `xbs` to
    *  a pair of k(y), t(y) and a string over (X cup C), where
    *  `nft` can transition with (k, t) from q to r, by reading `xbs` outputting the string.
    */
  def possiblePreviousOf[Q, X, A, B](
      q: Q,
      r: Q,
      invTransA: Map[(Q, A), Set[(Q, B)]],
      invTransX: Map[(Q, X), Set[Q]], // At q2 reading x can lead to transX(q2, x)
      xas: Cupstar[X, A]
  ): Set[(Map[X, (Q, Q)], Cupstar[X, B])] = {
    // `acc` accumulates a set of pairs of a mapping and configuration (outputs are reversed).
    xas
      .foldRight[Set[(Map[X, (Q, Q)], (Q, Cupstar[X, B]))]](
        Set((Map.empty, (r, Nil)))
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
    import Concepts._

    type NQ = (Q1, Map[X, (Q2, Q2)])

    val invTrans: Map[Q1, Set[(Q1, A, Update[X, B])]] =
      graphToMap(n1.edges) { case (q, a, m, r) => r -> (q, a, m) }

    val invTransB: Map[(Q2, B), Set[(Q2, Update[Y, C])]] =
      graphToMap(n2.edges) { case (q, b, m, r) => (r, b) -> (q, m) }

    // Consider product construction of two NSSTs.
    // invTransX(p)(q, x) is a set of state `r`s where q may transition to r by reading
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
          case Cop2(b) => n2.transOne(q, b).map { case (r, m) => (r, List(Cop2(m))) }
        }
      var updated = false
      do {
        updated = false
        // q1 =[???/m]=> r1, q2 =[(m(x)@q1)/???]=> r2 then q2 =[(x@r1)/???]=> r2
        for ((q1, _, m, r1) <- n1.edges; x <- n1.variables; q2 <- n2.states) {
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

    def previousStates(nq: NQ): Set[(NQ, A, Update[X, Update[Y, C]])] = {
      val (r, kt) = nq
      invTrans(r).flatMap {
        case (q, a, m) => {
          val candidates: List[(X, Set[(Map[X, (Q2, Q2)], Cupstar[X, Update[Y, C]])])] =
            kt.keySet
              .map(x =>
                x -> {
                  val (k, t) = kt(x)
                  // Variables always empty at state q can be ignored
                  val usedAtQ = n1.nonEmptyVarsAt(q)
                  val filtered = m(x).filter { case Cop1(x) => usedAtQ contains x; case _ => true }
                  possiblePreviousOf(k, t, invTransB, invTransX(q), filtered)
                }
              )
              .toList
          def aux(
              candidates: List[(X, Set[(Map[X, (Q2, Q2)], Cupstar[X, Update[Y, C]])])]
          ): Set[(Map[X, (Q2, Q2)], Update[X, Update[Y, C]])] =
            candidates match {
              case Nil => Set((Map.empty, n1.variables.map(x => x -> Nil).toMap))
              case (x, s) :: tl =>
                for ((kt1, mu) <- aux(tl); (kt2, alpha) <- s)
                  yield (
                    (kt1 ++ kt2),
                    mu + (x -> alpha)
                  )
            }
          aux(candidates).map {
            case (kt, m) => ((q, kt), a, m ++ Map.from((n1.variables -- m.keySet).map(x => x -> Nil)))
          }
        }
      }
    }

    val outF: Map[NQ, Set[(Cupstar[X, Update[Y, C]], Cupstar[Y, C])]] = {
      val outF1 = n1.outF.toList
      val outF2 = n2.outF.toList
      val graph =
        for ((q1, s1) <- outF1;
             xbs <- s1;
             (q2, s2) <- outF2;
             (kt, xms) <- {
               val usedAtQ1 = n1.nonEmptyVarsAt(q1)
               val filtered = xbs.filter { case Cop1(x) => usedAtQ1 contains x; case _ => true }
               possiblePreviousOf(n2.q0, q2, invTransB, invTransX(q1), filtered)
             };
             ycs <- s2)
          yield (q1, kt) -> (xms, ycs)
      graphToMap(graph) { case (k, v) => k -> v }
    }

    var states = outF.keySet
    var edges: List[(NQ, A, Update[X, Update[Y, C]], NQ)] = Nil
    var stack: List[NQ] = states.toList
    while (stack.nonEmpty) {
      val r = stack.head
      stack = stack.tail
      previousStates(r).foreach {
        case (q, a, m) => {
          edges ::= ((q, a, m, r))
          if (!states.contains(q)) {
            states += q
            stack ::= q
          }
        }
      }
    }

    val initialStates =
      states.filter { case (q, kt) => q == n1.q0 && kt.forall { case (_, (k, t)) => k == t } }

    // Remove all unreachable states.
    val reachables = closure[NQ](initialStates, graphToMap(edges) { case (q, _, _, r) => q -> r })

    val before = states.size
    val after = reachables.size
    val ratio = after.toDouble / before.toDouble
    println(f"After / Before: ${ratio}%.03f\tBefore: ${before}\tAfter: ${after}")

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

    new MSST[NWQ, A, C, X, Y](
      newStates,
      n1.in,
      n1.variables,
      n2.variables,
      graphToMap(newEdges) { case (q, a, m, r) => (q, a) -> (r, m) },
      None,
      newOutF
    )
  }
  // End of composeNsstsToMsst

  def composeNsstsToNsst[Q1, Q2, A, B, C, X, Y](
      n1: NSST[Q1, A, B, X],
      n2: NSST[Q2, B, C, Y]
  ): NSST[(Option[(Q1, Map[X, (Q2, Q2)])], Map[X, Concepts.M1[Y]]), A, C, (X, Y, Boolean)] = {
    if (!n1.isCopyless) {
      throw new Exception(s"Tried to compose NSST, but first NSST was copyfull: ${n1.edges}")
    }
    if (!n2.isCopyless) {
      throw new Exception(s"Tried to compose NSST, but second NSST was copyfull: ${n2.edges}")
    }
    MSST.convertMsstToNsst(NSST.composeNsstsToMsst(n1, n2))
  }

  def countOf2[A, B](alpha: Cupstar[A, B]): Map[B, Int] =
    erase1(alpha)
      .groupBy(identity)
      .map { case (b, l) => b -> l.length }
      .withDefaultValue(0)
  def countCharOfX[X, A](m: Update[X, A]): Map[X, Map[A, Int]] =
    m.map { case (x, alpha) => x -> countOf2(alpha) }

  /** Convert given NSST to NFT that transduces each input to its Parikh image. */
  def convertNsstParikhNft[Q, A, B, X](
      nsst: NSST[Q, A, B, X]
  ): MNFT[(Q, Set[X]), A, Map[B, Int]] = {
    type NQ = (Q, Set[X])
    type O = Map[B, Int]
    // Returns a set of p' s.t. string containing p' updated by m will contain p.
    def invert(m: Update[X, B], p: Set[X]): Set[Set[X]] = {
      // Map from x to a set of variables in m(x).
      val varsOf: Map[X, Set[X]] = Map.from {
        for ((x, xbs) <- m) yield x -> (erase2(xbs).toSet)
      }
      // Map from y to x s.t. m(x) contains y.
      // Because m is copyless, x is unique for each y.
      val inverse: Map[X, X] = Map.from {
        for ((x, ys) <- varsOf; y <- ys)
          yield y -> x
      }
      val must = for (y <- p if inverse.isDefinedAt(y)) yield inverse(y)
      if (must.flatMap(varsOf(_)) != p) {
        return Set.empty
      }
      val empties = varsOf.withFilter { case (x, xs) => xs.isEmpty }.map(_._1).toSet
      empties
        .subsets()
        .map(must ++ _)
        .toSet
    }
    val out: List[B] = nsst.out.toList
    implicit val monoid: Monoid[Map[B, Int]] = Monoid.vectorMonoid(out)
    // Ψ_{Gamma}^m in paper
    def nextStates(nq: NQ, a: A): Set[(NQ, O)] = {
      val (q1, p1) = nq
      Set.from {
        for ((q2, m) <- nsst.transOne(q1, a); p2 <- invert(m, p1))
          yield {
            val v = {
              val countInM = countCharOfX(m)
              // toList is necesasry because it is possible be that two varibles give the same vector.
              Monoid.fold(p2.toList.map(countInM(_)))
            }
            ((q2, p2), v)
          }
      }
    }
    val initials = nsst.variables.subsets().map((nsst.q0, _)).toSet
    var newStates: Set[NQ] = initials
    var newEdges: Map[(NQ, A), Set[(NQ, O)]] = Map.empty
    var stack: List[NQ] = newStates.toList
    while (stack.nonEmpty) {
      val q = stack.head
      stack = stack.tail
      for (a <- nsst.in) {
        val edges = nextStates(q, a)
        newEdges += (q, a) -> edges
        val newOnes = edges.map(_._1) -- newStates
        newStates ++= newOnes
        stack = newOnes.toList ++ stack
      }
    }
    val acceptF: Map[NQ, Set[O]] = Map.from {
      for ((q, p) <- newStates)
        yield (q, p) -> {
          for (alpha <- nsst.outF(q) if erase2(alpha).toSet == p)
            yield countOf2(alpha)
        }
    }
    new MNFT[NQ, A, O](
      newStates,
      nsst.in,
      newEdges,
      initials,
      acceptF
    ).optimized
  }

  def parikhImagePresburger[Q, A, B, X](n: NSST[Q, A, B, X]) = {
    import Parikh._
    val coutingNft = NSST.convertNsstParikhNft(n)
    val formula = Parikh.parikhMnftToPresburgerFormula(coutingNft)
    type E = (Int, Image[B], Int)
    type X = EnftVar[Int, B, E]
    class Renamer() {
      var i = 0
      private def newVar() = {
        i += 1
        i
      }
      var eMap: Map[E, String] = Map.empty
      var qMap: Map[Int, String] = Map.empty
      def renamer(x: X): String = x match {
        case BNum(b) => s"y${b}"
        case ENum(e) => eMap.getOrElse(e, { val s = s"x${newVar()}"; eMap += e -> s; s })
        case Dist(q) => qMap.getOrElse(q, { val s = s"x${newVar()}"; qMap += q -> s; s })
      }
    }
    Formula.renameVars(formula, new Renamer().renamer _)
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
class MNFT[Q, A, M: Monoid](
    val states: Set[Q],
    val in: Set[A],
    partialEdges: Map[(Q, A), Set[(Q, M)]],
    val initials: Set[Q],
    partialF: Map[Q, Set[M]]
) {
  val edges = partialEdges.withDefaultValue(Set.empty)
  val acceptF = partialF.withDefaultValue(Set.empty)
  def transOne(q: Q, a: A): Set[(Q, M)] = edges((q, a))
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
        edges.map { case ((q, _), s) => q -> s.map(_._1) }.withDefaultValue(Set.empty)
      )
    val invReachable = {
      val invEdges = edges.toList
        .map { case ((q, _), s) => (q, s) }
        .flatMap { case (q, s) => s.map { case (r, _) => (r, q) } }
        .groupBy(_._1)
        .view
        .mapValues(_.map(_._2).toSet)
        .toMap
        .withDefaultValue(Set.empty)
      Concepts.closure(partialF.filter { case (q, s) => s.nonEmpty }.keySet, invEdges)
    }
    val newEdges = edges
      .flatMap {
        case ((q, a), s) =>
          if (invReachable contains q) {
            Map((q, a) -> s.filter { case (q, _) => invReachable contains q })
          } else Map.empty
      }
    new MNFT[Q, A, M](
      invReachable,
      in,
      newEdges,
      initials intersect invReachable,
      acceptF.filter { case (q, _) => invReachable contains q }
    )
  }

  def toENFT: ENFT[Int, A, M] = {
    trait NQ
    case class OfQ(q: Q) extends NQ
    case object Init extends NQ // New initial state
    case object Fin extends NQ // New final state
    val newStates = states.map[NQ](OfQ.apply) + Init + Fin
    type Edge = ((NQ, Option[A]), Set[(NQ, M)])
    val newEdges: Iterable[Edge] = {
      val fromInit: Edge =
        (Init, None) -> initials.map(q => (OfQ(q), implicitly[Monoid[M]].unit)).toSet
      val toFinal: Iterable[Edge] = {
        for (q <- acceptF.keySet)
          yield (OfQ(q), None) -> acceptF(q).map((Fin, _)).toSet
      }
      edges
        .map[Edge] { case ((q, a), s) => ((OfQ(q), Some(a)), s.map { case (r, m) => (OfQ(r), m) }) } ++
        toFinal ++
        Iterable(fromInit)
    }
    new ENFT[NQ, A, M](
      newStates,
      in,
      newEdges.toMap,
      Init,
      Fin
    ).renamed
  }

  def unifyInitAndFinal = toENFT
}

/** Monoid NFT with epsilon transition.
  * Inital state and final state of this class Must be singleton.
  */
class ENFT[Q, A, M: Monoid](
    val states: Set[Q],
    val in: Set[A],
    partialEdges: Map[(Q, Option[A]), Set[(Q, M)]],
    val initial: Q,
    val finalState: Q
) {
  val edges = partialEdges.withDefaultValue(Set.empty)
  def renamed: ENFT[Int, A, M] = {
    val stateMap = (states zip LazyList.from(0)).toMap
    val newEdges =
      for (((q, a), s) <- partialEdges)
        yield (stateMap(q), a) -> s.map { case (q, m) => (stateMap(q), m) }
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
          edges((q, o)).flatMap {
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
  import Concepts._
  import Monoid.fold
  type Edges[Q, A, B, X, Y] = Map[(Q, A), Set[(Q, Update[X, Update[Y, B]])]]

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
      fold(ms)
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
        stack = newOnes.toList ++ stack
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

private class RegExp2NFA[A](re: RegExp[A], alphabet: Set[A]) {
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
