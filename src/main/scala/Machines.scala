package com.github.kmn4.sst

class NSST[Q, A, B, X](
  val states: Set[Q],
  val in: Set[A],
  val out: Set[B],
  val variables: Set[X],
  val edges: NSST.Edges[Q, A, X, B],
  val q0: Q,
  val outF: Map[Q, NSST.Output[X, B]]
) {
  import NSST._
  implicit val monoid: Monoid[Update[X, B]] = variables
  def trans(q: Q, a: A): Set[(Q, Update[X, B])] = edges.withDefaultValue(Set.empty)((q, a))
  def transduce(w: List[A]): Set[List[B]] =
    Monoid.transition(q0, w, trans).flatMap{ case (q, m) => outputAt(q, m).toSet }
  def outputAt(q: Q, m: Update[X, B]): Option[List[B]] =
    outF.get(q).map { Cop.flatMap1(_, m) }.map { eraseVar }

  def asNFA: NFA[Q, A] = new NFA(
    states,
    in,
    edges.map{ case ((q, a) -> s) => (q, Some(a)) -> s.map(_._1) },
    q0,
    outF.keySet
  )
}

object NSST {
  type Update[X, B] = Map[X, Output[X, B]]
  type Edges[Q, A, X, B] = Map[(Q, A), Set[(Q, Update[X, B])]]
  type Output[X, B] = List[Cop[X, B]]
  implicit def updateMonoid[X, B](xs: Iterable[X]): Monoid[Update[X, B]] = new Monoid[Update[X, B]] {
    def combine(m1: Update[X, B], m2: Update[X, B]): Update[X, B] =
      for ((k, v) <- m2) yield (k -> Cop.flatMap1(v, m1(_)))
    def unit: Update[X, B] = Map.from(xs.map(x => x -> List(Cop1[X, B](x))))
  }
  def eraseVar[X, B](l: Output[X, B]): List[B] = Cop.erase1(l)

  // Type of states of composed NSST without initial one.
  type ComposedQ[Q1, Q2, X] = (Q1, Map[X, (Q2, Q2)])
  // Sequentially compose given NSST and NFT.
  // TODO Currently if a given NSST has more than 2 variables this function
  // take too long to return. It is likely that this is because the algorithm
  // makes and considers all states ((Q2 * Q2 + 1)^X) when calculating
  // next states of a given state.
  // It may be that the number of states to consider can be reduced.
  def composeNsstAndNft[A, B, C, Q1, X, Q2](
    nsst: NSST[Q1, A, B, X],
    nft: NFT[Q2, B, C]
  ): NSST[Option[ComposedQ[Q1, Q2, X]], A, C, X] = {
    type NoOp = ComposedQ[Q1, Q2, X]
    type NewQ = Option[NoOp]

    def transitionWith(kt: Map[X, (Q2, Q2)])(q: Q2, w: Output[X, B]) = {
      def transWithKT(q: Q2, sigma: Cop[X, B]): Set[(Q2, Output[X, C])] = sigma match {
        case Cop1(x) => kt.get(x).flatMap{
          case (k, t) => if (q == k) Some((t, List(Cop1[X, C](x)))) else None
        }.toSet
        case Cop2(a) => nft.trans(q, a).map{ case (q, w) => (q, w.map(Cop2(_))) }
      }
      Monoid.transition(q, w, transWithKT)
    }

    // Returns a set of Maps which maps x in domain to an element in g(x).
    def mapsWhoseDomainIsAndValueIsIn[X, A](
      g: X => Iterable[A],
      domain: Iterable[X]
    ): Set[Map[X, A]] = {
      def aux(g: X => Iterable[A], domain: List[X]): Set[Map[X, A]] = domain match {
        case Nil => Set(Map())
        case hd :: tl => {
          val fs = aux(g, tl)
          val added = g(hd).map(hd -> _)
          fs.flatMap(m => added.map(m + _))
        }
      }
      aux(g, domain.toList)
    }

    // Returns a set of function f s.t. domain ⊂ dom(f) ⊂ universe
    // and f ∈ createFunctions(dom(f)).
    def mapsWhoseDomainContains[X, A](
      createFunctions: Set[X] => Set[Map[X, A]],
      domain: Set[X],
      universe: Set[X]
    ): Set[Map[X, A]] = {
      val diff = universe -- domain
      diff
        .subsets
        .flatMap(s => createFunctions(domain ++ s))
        .toSet
    }

    // Returns a set of function f s.t. domain ⊂ dom(f) ⊂ universe
    // and f(x) ∈ g(x).
    def mapsWhoseDomainContiansAndValueIsIn[X, A](
      g: X => Iterable[A],
      domain: Set[X],
      universe: Set[X]
    ): Set[Map[X, A]] = mapsWhoseDomainContains(
      mapsWhoseDomainIsAndValueIsIn(g, _),
      domain,
      universe
    )

    def nextStates(q: NoOp, a: A): Set[(NoOp, Update[X, C])] = {
      val (q1, kt) = q
      // Evaluates to mapping from variable x to the set of (k'(x), t'(x), m(x))
      // where using kt, k'(x) can transition by m1(x) to t'(x) yielding m(x).
      def transitionByM1(m1: Update[X, B])
          : Map[X, Set[(Q2, Q2, Output[X, C])]] = {
        def transitionByM1x(x: X): Set[(Q2, Q2, Output[X, C])] = {
          nft
            .states
            .flatMap(p => transitionWith(kt)(p, m1(x)).map{ case (q, m) => (p, q, m) })
        }
        nsst.variables.map(x => x -> transitionByM1x(x)).toMap
      }
      // Set of variables that kt of next state must include under m1.
      def mustInclude(m1: Update[X, B]): Set[X] =
        nsst.variables.filter(x => {
                                val xs = Cop.erase2(m1(x)).toSet
                                xs.nonEmpty && xs.subsetOf(kt.keySet)
                              } )

      val nested =
      for ((q1p, m1) <- nsst.trans(q1, a)) yield {
        mapsWhoseDomainContiansAndValueIsIn(
          transitionByM1(m1)(_),
          mustInclude(m1),
          nsst.variables
        ).map(m => (m.map{ case (x, (k, t, _)) => x -> (k, t) },
                    m.map{ case (x, (_, _, m)) => x -> m }.withDefaultValue(Nil)))
          .map{ case (kt, m) => ((q1p, kt), m) }
      }
      nested.flatten
    } // End of nextStates

    def nextStatesNewQ(q: NewQ, a: A): Set[(NewQ, Update[X, C])] = q match {
      case Some(q) => nextStates(q, a).map{ case (q, m) => (Some(q), m) }
      case None => {
        val kkList: List[Map[X, (Q2, Q2)]] = {
          val q2pair = (for (q2 <- nft.states) yield Some((q2, q2)))
            .toList
            .appended(None)
          def enumerate(size: Int): List[List[Option[(Q2, Q2)]]] =
            if (size == 0) List(Nil)
            else for (
              p <- q2pair;
              ps <- enumerate(size-1)
            ) yield p :: ps
          val permutations = enumerate(nsst.variables.size)
          permutations
            .map(pairs => (nsst.variables zip pairs).flatMap{
                   case (x, Some(p)) => List((x, p))
                   case _ => Nil
                 }.toMap)
            .toList
        }
        (for (kk <- kkList) yield nextStates((nsst.q0, kk), a))
          .flatMap{ s => s.map[(NewQ, Update[X, C])]{ case (q, m) => (Some(q), m) } }
          .toSet
      }
    }

    val initial: NewQ = None
    var newStates: Set[NewQ] = Set(initial)
    var newEdges: Map[(NewQ, A), Set[(NewQ, Update[X, C])]] = Map()
    var stack = List(initial)
    while (stack.nonEmpty) {
      val q = stack.head
      stack = stack.tail
      for (a <- nsst.in) {
        val edges = nextStatesNewQ(q, a)
        newEdges += (q, a) -> edges
        val newOnes = edges.map(_._1) -- newStates
        newStates ++= newOnes
        stack = newOnes.toList ++ stack
      }
    }
    val newOutF = {
      for (q <- newStates) yield q -> {
        q match {
          case Some((q1, kt)) => {
            nsst.outF.get(q1).flatMap{
              alpha => {
                val s = transitionWith(kt)(nft.q0, alpha)
                  .filter{ case (q2, _) => nft.finals contains q2 }
                if (s.nonEmpty) Some(s.head._2)
                else None
              } }
          }
          case None => {
            nsst.outF.get(nsst.q0).flatMap{
              alpha => {
                val s = nft.transduce(eraseVar(alpha))
                if (s.nonEmpty) Some(s.head.map(Cop2[X, C](_)))
                else None
              }
            }
          }
        }
      }
    }
      .flatMap{
        case (q, Some(l)) => Set((q, l))
        case (q, None) => Set()
      }
      .toMap

    // Only states reachable from domain of F
    // by inverse edges are needed.
    val inverse =
      newEdges
        .toList
        .flatMap{ case ((q, _), s) => s.map{ case (r, _) => (r, q) } }
        .groupBy(_._1)
        .map{ case (k, v) => k -> v.map(_._2).toSet }
        .withDefaultValue(Set())
    def transInv(qs: Set[NewQ]): Set[NewQ] =
      qs.foldLeft(Set[NewQ]()){ case (acc, q) => acc union inverse(q) }
    var invNewOnes = newOutF.keySet
    var invReachables = invNewOnes
    while (invNewOnes.nonEmpty) {
      invNewOnes = transInv(invNewOnes) -- invReachables
      invReachables ++= invNewOnes
    }
    newStates = invReachables
    newEdges =
      newEdges.flatMap{ case ((p, a), s) =>
        if (newStates contains p) {
          Map((p, a) -> s.filter{ case (q, _) => newStates contains q })
        } else Map()
      }
    new NSST(
      newStates,
      nsst.in,
      nft.out,
      nsst.variables,
      newEdges,
      None,
      newOutF.filter{ case (p, _) => newStates contains p }
    )
  } // End of composeNsstAndNft

  def apply(
    states: Iterable[Int],
    vars: Iterable[Char],
    edges: Iterable[(Int, Char, Iterable[(Int, Iterable[String])])],
    q0: Int,
    outF: Iterable[(Int, String)]
  ): NSST[Int, Char, Char, Char] = {
    def stringToOutput(s: String): Output[Char, Char] =
      s.map[Cop[Char, Char]]{ c => if (c.isUpper) Cop1(c) else Cop2(c) }.toList
    val newEdges =
      edges
        .map{
          case (p, a, l) => {
            (p, a) ->
            l.map{ case (q, m) =>
              (q, m.map{ s => s.head -> stringToOutput(s.substring(2)) }.toMap) }
              .toSet
          }
        }
        .toMap
    val newF = outF.map{ case (q, s) => q -> stringToOutput(s) }.toMap
    new NSST(
      states.toSet,
      edges.map(_._2).toSet,
      Set(), // TODO
      vars.toSet,
      newEdges,
      q0,
      newF
    )
  }
}

class NFT[Q, A, B](
  val states: Set[Q],
  val in: Set[A],
  val out: Set[B],
  val edges: NFT.Edges[Q, A, B],
  val q0: Q,
  val finals: Set[Q]
) {
  def trans(q: Q, a: A): Set[(Q, List[B])] = edges.withDefaultValue(Set.empty)((q, a))
  def transduce(w: List[A]): Set[List[B]] =
    Monoid.transition(q0, w, trans).filter{ case (q, _) => finals contains q }.map(_._2)
}

object NFT {
  type Edges[Q, A, B] = Map[(Q, A), Set[(Q, List[B])]]

  def apply(
    states: Iterable[Int],
    edges: Iterable[(Int, Char, Int, String)],
    q0: Int,
    finals: Set[Int]
  ): NFT[Int, Char, Char] = {
    new NFT(
      states.toSet,
      edges.map(_._2).toSet,
      Set(),
      edges
        .map{ case (p, a, q, s) => (p, a) -> (q, s.toList) }
        .groupBy(_._1)
        .map{ case (k, v) => k -> v.map(_._2).toSet }
        .toMap,
      q0,
      finals
    )
  }
}

class DFA[Q, A]
(
  val states: Set[Q],
  val alpha: Set[A],
  val transition: Map[(Q, A), Q],
  val q0: Q,
  val finalStates: Set[Q]
) {

  def trans(q: Q, w: List[A]): Q =
    w match {
      case Nil => q
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
    val newTransition: Map[(Int, A), Int] = (
      for (i <- newStates; a <- alpha) yield {
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

class NFA[Q, A]
(
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
