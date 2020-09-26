package com.github.kmn4.sst

/**
  * Types and functions relatively independent of concrete machines.
  */
object Concepts {
  type Cupstar[X, B] = List[Cop[X, B]]
  type Update[X, B] = Map[X, Cupstar[X, B]]
  implicit def updateMonoid[X, B](xs: Iterable[X]): Monoid[Update[X, B]] = new Monoid[Update[X, B]] {
    def combine(m1: Update[X, B], m2: Update[X, B]): Update[X, B] = Map.from {
      for (x <- xs) yield (x -> flatMap1(m2(x), m1(_)))
    }
    def unit: Update[X, B] = Map.from(xs.map(x => x -> List(Cop1(x))))
  }
  def flatMap1[A, B, C](abs: Cupstar[A, B], f: A => Cupstar[C, B]): Cupstar[C, B] =
    abs.flatMap{ case Cop1(a) => f(a); case Cop2(b) => List(Cop2(b)) }
  def erase1[A, B](abs: Cupstar[A, B]): List[B] = abs.flatMap(Cop.erase1(_))
  def erase2[A, B](abs: Cupstar[A, B]): List[A] = abs.flatMap(Cop.erase2(_))

  type M1[X] = Map[X, List[X]]
  type M2[X, A] = Map[(X, Boolean), List[A]]
  def gamma[X, A](
    xs: Set[X]
  )(
    permutation: M1[X],
    prePost: M2[X, A],
  ): Update[X, A] = {
    val (front, back) = xs.map(x =>
      (x -> prePost((x, false)).map(Cop2(_)).appended(Cop1(x)),
       x -> (Cop1(x) :: prePost((x, true)).map(Cop2(_))))
    ).unzip
    val mid: Update[X, A] = permutation.map { case (x, xs) => x -> xs.map(Cop1(_)) }
    Monoid.fold(List(front.toMap, mid, back.toMap))(xs)
  }

  def proj[X, A](m: Update[X, A]): (M1[X], M2[X, A]) = {
    def aux(x: X, l: List[Cop[X, A]]): M2[X, A] = {
      l.foldRight(List((x, true) -> List[A]())) {
        case (Cop1(x), acc) => ((x, false) -> Nil) :: acc
        case (Cop2(a), (xb, as) :: acc) => (xb -> (a :: as)) :: acc
        case _ => throw new Exception("This must not happen")
      }.toMap
    }

    (
      m.map { case (x, xas) => x -> erase2(xas) }.withDefaultValue(Nil),
      m.flatMap { case (x, xas) => aux(x, xas) }.withDefaultValue(Nil)
    )
  }

  def closure[Q](start: Set[Q], edges: Q => Set[Q]): Set[Q] = {
    def trans(qs: Set[Q]): Set[Q] =
      qs.foldLeft(Set.empty[Q]){ case (acc, q) => acc union edges(q) }
    var newQs = start
    var clos = start
    while (newQs.nonEmpty) {
      newQs = trans(newQs) -- clos
      clos ++= newQs
    }
    clos
  }

}

/** Nondeterministic streaming string transducer */
class NSST[Q, A, B, X](
  val states: Set[Q],
  val in: Set[A],
  val variables: Set[X],
  edgesArg: NSST.Edges[Q, A, X, B],
  val q0: Q,
  val partialF: Map[Q, Set[Concepts.Cupstar[X, B]]]
) {
  import NSST._
  import Concepts._

  val edges: NSST.Edges[Q, A, X, B] = {
    edgesArg
      .view
      .mapValues(s => s.filter{ case (q, _) => states contains q })
      .filter{ case ((q, _), _) => states contains q }
      .toMap
  }

  implicit val monoid: Monoid[Update[X, B]] = variables
  val outF: Map[Q, Set[Cupstar[X, B]]] = partialF.withDefaultValue(Set())
  val out: Set[B] = Set.from {
    for ((_, s) <- edges;
         (_, m) <- s;
         (_, alpha) <- m;
         b <- erase1(alpha))
    yield b
  }

  def trans(q: Q, a: A): Set[(Q, Update[X, B])] = edges.withDefaultValue(Set.empty)((q, a))
  def transduce(w: List[A]): Set[List[B]] =
    Monoid.transition(Set(q0), w, trans).flatMap{ case (q, m) => outputAt(q, m).toSet }
  def outputAt(q: Q, m: Update[X, B]): Set[List[B]] =
    outF(q).map{ flatMap1(_, m) }.map(erase1)

  def asNFA: NFA[Q, A] = new NFA(
    states,
    in,
    edges.map{ case ((q, a) -> s) => (q, Some(a)) -> s.map(_._1) },
    q0,
    outF.keySet
  )

  def isCopyless: Boolean = {
    val e = edges.flatMap{ case (_, s) => s }.forall{ case (_, m) => NSST.isCopylessUpdate(m) }
    val f = outF.forall { case (_, s) => s.forall(isCopylessOutput(_)) }
    e && f
  }

  def asMonoidNFT: NFT[Q, A, Update[X, B]] = new NFT(
    states,
    in,
    edges.view.mapValues{ _.map{ case (r, m) => (r, List(m)) } }.toMap,
    q0,
    outF.filter { case (q, s) => s.nonEmpty }.keySet
  )

  def isEmpty: Boolean = {
    val reachables = closure(
      Set(q0),
      edges
        .toList
        .groupBy(_._1._1)
        .view
        .mapValues(_.flatMap{ case (_, s) => s.map(_._1)}.toSet)
        .toMap
        .withDefaultValue(Set.empty)
    )
    (reachables intersect partialF.filter{ case (_, s) => s.nonEmpty }.map(_._1).toSet).isEmpty
  }

  def renamed: NSST[Int, A, B, Int] = {
    val stateMap = (states zip LazyList.from(0)).toMap
    val varMap = (variables zip LazyList.from(0)).toMap
    val newEdges =
      edges
        .map{ case ((q, a), s) => (stateMap(q), a) ->
                 s.map { case (r, m) => {
                          (
                            stateMap(r),
                            m.map { case (x, xb) => (varMap(x), xb.map(_.map1(varMap))) }
                          )
                        } }
        }
    val newF =
      partialF
        .map { case (q, s) => (
                stateMap(q),
                s.map { xb => xb.map(_.map1(varMap)) }
              ) }
    new NSST(
      stateMap.map(_._2).toSet,
      in,
      varMap.map(_._2).toSet,
      newEdges,
      stateMap(q0),
      newF
    )
  }
}

object NSST {
  import Concepts._
  type Edges[Q, A, X, B] = Map[(Q, A), Set[(Q, Update[X, B])]]
  def isCopylessUpdate[X, B](update: Update[X, B]): Boolean = {
    val vars = update.keySet
    def count(x: X): Int = update.foldLeft(0){
      case (acc, (_ , rhs)) => acc + rhs.foldLeft(0) {
        case (acc, Cop1(y)) if y == x => acc + 1
        case (acc, _) => acc
      }
    }
    vars.forall(count(_) <= 1)
  }
  def isCopylessOutput[X, A](output: Cupstar[X, A]): Boolean = {
    output.foldLeft((true, Set[X]())) {
      case ((b, s), Cop1(x)) => (b || s.contains(x), s + x)
      case ((b, s), Cop2(a)) => (b, s)
    }._1
  }

  // Returns a set of pairs of state and string over X cup B such that
  // nft can transition to from q by w with kt.
  def transitionWith[Q, A, B, X](nft: NFT[Q, A, B], kt: Map[X, (Q, Q)])(q: Q, w: Cupstar[X, A]) = {
    def transWithKT(q: Q, sigma: Cop[X, A]): Set[(Q, Cupstar[X, B])] = sigma match {
      case Cop1(x) => kt.get(x).flatMap{
        case (k, t) => if (q == k) Some((t, List(Cop1(x)))) else None
      }.toSet
      case Cop2(a) => nft.trans(q, a).map{ case (q, w) => (q, w.map(Cop2(_))) }
    }
    Monoid.transition(Set(q), w, transWithKT)
  }

  // Type of states of composed NSST without initial one.
  type ComposedQ[Q1, Q2, X] = (Q1, Map[X, (Q2, Q2)])
  // Sequentially compose given NSST and NFT.
  def composeNsstAndNft[A, B, C, Q1, X, Q2](
    nsst: NSST[Q1, A, B, X],
    nft: NFT[Q2, B, C]
  ): NSST[Option[ComposedQ[Q1, Q2, X]], A, C, X] = {
    if (!nsst.isCopyless) {
      throw new Exception("Tried to compose copyfull NSST with NGSM.")
    }

    // New states
    type NQ = ComposedQ[Q1, Q2, X]
    // New states wrapped by Option
    type WNQ = Option[NQ]

    // Returns a set of function f s.t. dom(f) = domain and ∀ x in domain, f(x) ∈ g(x).
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

    /** Returns a set of function f s.t. domain ⊂ dom(f) ⊂ universe
      * and f ∈ createFunctions(dom(f)). */
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
    def mapsWhoseDomainContainsAndValueIsIn[X, A](
      g: X => Iterable[A],
      domain: Set[X],
      universe: Set[X]
    ): Set[Map[X, A]] = mapsWhoseDomainContains(
      mapsWhoseDomainIsAndValueIsIn(g, _),
      domain,
      universe
    )

    def nextStates(q: NQ, a: A): Set[(NQ, Update[X, C])] = {
      val (q1, kt) = q
      // Evaluates to mapping from variable x to the set of (k'(x), t'(x), m(x))
      // where using kt, k'(x) can transition by m1(x) to t'(x) yielding m(x).
      def transitionByM1(m1: Update[X, B])
          : Map[X, Set[(Q2, Q2, Cupstar[X, C])]] = {
        def transitionByM1x(x: X): Set[(Q2, Q2, Cupstar[X, C])] = {
          val transWithKT = transitionWith(nft, kt) _
          for (p <- nft.states;
               (q, m) <- transWithKT(p, m1(x)))
            yield (p, q, m)
        }
        nsst.variables.map(x => x -> transitionByM1x(x)).toMap
      }
      // Set of variables that kt of next state must include under m1.
      def mustInclude(m1: Update[X, B]): Set[X] =
         nsst.variables.filter(x => {
                               val xs = erase2(m1(x)).toSet
                               xs.nonEmpty && xs.subsetOf(kt.keySet)
                             } )
      def empties(m1: Update[X, B]): Set[X] = nsst.variables.filter(x => erase2(m1(x)).toSet.isEmpty)

      val nested =
        for ((q1p, m1) <- nsst.trans(q1, a)) yield {
          val must = mustInclude(m1)
          // If `must` updated by m1 does not give domain of current kt,
          // then one cannot transition by m1.
          if (must.flatMap(x => erase2(m1(x))) != kt.keySet) return Set()
          mapsWhoseDomainContainsAndValueIsIn(
            transitionByM1(m1)(_),
            must,
            must ++ empties(m1)
          ).map(possibleKTM => (
                  possibleKTM.map{ case (x, (k, t, _)) => x -> (k, t) },
                  possibleKTM.map{ case (x, (_, _, m)) => x -> m }.withDefaultValue(Nil)
                )).map{ case (kt, m) => ((q1p, kt), m) }
        }
      nested.flatten
    } // End of nextStates

   val initialStates: Set[NQ] = {
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
     kkList.map(k0 => (nsst.q0, k0)).toSet
   }
   var newStates: Set[NQ] = initialStates
   var newEdges: Map[(NQ, A), Set[(NQ, Update[X, C])]] = Map()
   var stack = initialStates.toList
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
   val newOutF: Map[NQ, Set[Cupstar[X, C]]] = {
     for ((q1, kt) <- newStates)
     yield (q1, kt) -> {
       for (gamma <- nsst.outF(q1);
            (q2, alpha) <- transitionWith(nft, kt)(nft.q0, gamma)
            if nft.finals contains q2)
       yield alpha
     }
   }.toMap

   // Only states reachable from domain of F
   // by inverse edges are needed.
   val inverse =
     newEdges
       .toList
       .flatMap{ case ((q, _), s) => s.map{ case (r, _) => (r, q) } }
       .groupBy(_._1)
       .map{ case (k, v) => k -> v.map(_._2).toSet }
       .withDefaultValue(Set())
   newStates = closure(
     newOutF.filter{ case (_, s) => s.nonEmpty }.keySet,
     inverse)
   newEdges =
     newEdges.flatMap{ case ((p, a), s) =>
       if (newStates contains p) {
         Map((p, a) -> s.filter{ case (q, _) => newStates contains q })
       } else Map()
     }

   // Wrap states with Option
   val newStatesWrapped: Set[WNQ] = newStates.map(Some(_)) ++ Set(None)
   val newEdgesWrapped = {
     val tmp: Edges[WNQ, A, X, C]
       = newEdges.map { case ((q, a), s) => (Some(q), a) -> s.map { case (r, m) => (Some(r), m) } }
     val fromNone =
       for (a <- nsst.in) yield (Option.empty, a) -> {
         initialStates.flatMap(q0 => tmp.withDefaultValue(Set.empty)(Some(q0), a))
       }
     tmp ++ fromNone
   }.toMap
   val newFWrapped = {
     val tmp: Map[WNQ, Set[Cupstar[X, C]]] =
       newOutF
         .withFilter { case (p, _) => newStates contains p }
         .map { case (p, s) => Some(p) -> s }
     val atNone: (WNQ, Set[Cupstar[X, C]]) = None -> {
       for (gamma <- nsst.outF(nsst.q0);
            cs <- nft.transduce(erase1(gamma))) yield cs.map(Cop2(_))
     }
     tmp + atNone
   }
   new NSST[WNQ, A, C, X](
     newStatesWrapped,
     nsst.in,
     nsst.variables,
     newEdgesWrapped,
     None,
     newFWrapped
   )
  } // End of composeNsstAndNft

  def composeMSST[Q1, Q2, A, B, C, X, Y](
    n1: NSST[Q1, A, B, X],
    n2: NSST[Q2, B, C, Y]
  ) = {
    val nft = n2.asMonoidNFT
    val msst = composeNsstAndNft[A, B, Update[Y, C], Q1, X, Q2](n1, nft)
    val msstF = msst
      .outF
      .map {
        case (q, s) => q -> {
          q match {
            case Some((q, kt)) => {
              for (gamma <- n1.outF(q);
                   (q2, alpha) <- transitionWith(nft, kt)(nft.q0, gamma);
                   beta <- n2.outF(q2))
              yield (alpha, beta)
            }
            case None => {
              for (gamma <- n1.outF(n1.q0);
                   cs <- n2.transduce(erase1(gamma)))
              yield (
                List.empty[Cop[X, Update[Y, C]]],
                cs.map[Cop[Y, C]](Cop2(_))
              )
            }
          }
        }}
    new MSST(
      msst.states,
      msst.in,
      msst.variables,
      n2.variables,
      msst.edges,
      msst.q0,
      msstF
    )
  }

  def composeNsstOfNssts[Q1, Q2, A, B, C, X, Y](n1: NSST[Q1, A, B, X], n2: NSST[Q2, B, C, Y]) = {
    if (!n1.isCopyless) {
      throw new Exception(s"Tried to compose NSST, but first NSST was copyfull: ${n1.edges}")
    }
    if (!n2.isCopyless) {
      throw new Exception(s"Tried to compose NSST, but second NSST was copyfull: ${n2.edges}")
    }
    MSST.convertMsstToNsst(composeMSST(n1, n2)).renamed
  }

  def countOf2[A, B](alpha: Cupstar[A, B]): Map[B, Int] =
    erase1(alpha)
      .groupBy(identity)
      .map { case (b, l) => b -> l.length }
      .withDefaultValue(0)
  def countCharOfX[X, A](m: Update[X, A]): Map[X, Map[A, Int]] =
    m.map { case (x, alpha) => x -> countOf2(alpha) }
  def convertNsstToCountingNft[Q, A, B, X](nsst: NSST[Q, A, B, X]): MNFT[(Q, Set[X]), A, Map[B, Int]] = {
    type NQ = (Q, Set[X])
    type O = Map[B, Int]
    // Returns a set of p' s.t. string containing p' updated by m will contain p.
    def invert(m: Update[X, B], p: Set[X]): Set[Set[X]] = {
      val varsOf: Map[X, Set[X]] = Map.from {
        for ((x, xbs) <- m) yield x -> (erase2(xbs).toSet)
      }
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
      empties.subsets()
        .map(must ++ _)
        .toSet
    }
    val out: List[B] = nsst.out.toList
    implicit val monoid: Monoid[Map[B, Int]] = Monoid.vectorMonoid(out)
    // Ψ_{Gamma}^m in paper
    def nextStates(nq: NQ, a: A): Set[(NQ, O)] = {
      val (q1, p1) = nq
      Set.from {
        for ((q2, m) <- nsst.trans(q1, a); p2 <- invert(m, p1))
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
    )
  }

  def parikhImage[Q, A, B, X](nsst: NSST[Q, A, B, X]): Semilinear[Map[B, Int]] = {
    val mnft = convertNsstToCountingNft(nsst)
    val regex = MNFT.outputRegex(mnft)
    val s = Semilinear.fromRegex(regex)(Monoid.vectorMonoid(nsst.out)(Monoid.intAdditiveMonoid))
    // Remove duplicate linear set
    Semilinear(s.ls.toSet.toList)
  }

  def apply(
    states: Iterable[Int],
    vars: Iterable[Char],
    edges: Iterable[(Int, Char, Iterable[(Int, Iterable[String])])],
    q0: Int,
    outF: Iterable[(Int, String)]
  ): NSST[Int, Char, Char, Char] = {
    def stringToCupstar(s: String): Cupstar[Char, Char] =
      s.map[Cop[Char, Char]]{ c => if (c.isUpper) Cop1(c) else Cop2(c) }.toList
    val newEdges =
      edges
        .groupBy { case (p, a, _) => (p, a) }
        .map { case ((p, a), l) => (p, a) ->
          l
            .flatMap(_._3)
            .map { case (q, m) => (
              q,
              m.map(s => s.head -> stringToCupstar(s.substring(2))).toMap
            )}
            .toSet
        }
    val newF = outF.map{ case (q, s) => q -> Set(stringToCupstar(s)) }.toMap
    new NSST(
      states.toSet,
      edges.map(_._2).toSet,
      vars.toSet,
      newEdges,
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
  def trans(q: Q, a: A): Set[(Q, List[B])] = edges.withDefaultValue(Set.empty)((q, a))
  def transduce(w: List[A]): Set[List[B]] =
    Monoid.transition(Set(q0), w, trans).filter{ case (q, _) => finals contains q }.map(_._2)
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
        .map{ case (p, a, q, s) => (p, a) -> (q, s.toList) }
        .groupBy(_._1)
        .map{ case (k, v) => k -> v.map(_._2).toSet }
        .toMap,
      q0,
      finals
    )
  }
}

/** Monoid NFT */
class MNFT[Q, A, M](
  val states: Set[Q],
  val in: Set[A],
  partialEdges: Map[(Q, A), Set[(Q, M)]],
  val initials: Set[Q],
  partialF: Map[Q, Set[M]],
  )(
  implicit val monoid: Monoid[M]
) {
  val edges = partialEdges.withDefaultValue(Set.empty)
  val acceptF = partialF.withDefaultValue(Set.empty)
  def trans(q: Q, a: A): Set[(Q, M)] = edges((q, a))
  def transduce(w: List[A]): Set[M] =
    for ((q, m) <- Monoid.transition(initials, w, trans);
         mf <- acceptF(q))
    yield monoid.combine(m, mf)

}

object MNFT {
  def outputRegex[Q, A, M](mnft: MNFT[Q, A, M]): RegExp[M] = {
    type NQ = Cop[Q, Boolean] // true: initial state, false: final state
    type E = Map[(NQ, NQ), RegExp[M]]
    var edges: E = {
      val graph = for (((q1, a), s) <- mnft.edges;
                       (q2, m) <- s)
                  yield ((Cop1(q1), Cop1(q2)), m)
      val fromInitial = mnft.initials.map(q0 => (Cop2(true), Cop1(q0)) -> EpsExp)
      def regexOf(l: Iterable[M]): RegExp[M] =
        l.map(CharExp(_)).foldLeft[RegExp[M]](EmptyExp){ case (acc, e) => OrExp(acc, e) }
      val toFinal: E = mnft.acceptF.withFilter{ case (_, s) => s.nonEmpty }
        .map{ case (qf, s) => (Cop1(qf), Cop2(false)) -> regexOf(s) }
      graph.toList
        .groupBy(_._1)
        .view
        .mapValues(l => regexOf(l.map{ case (_, m) => m }))
        .concat(fromInitial)
        .concat(toFinal)
        .toMap
    }
    val qs = mnft.states.map[NQ](Cop1(_))
    var nqs = qs + Cop2(true) + Cop2(false)
    for (q <- qs) {
      for (p <- nqs; r <- nqs if p != q && r != q) {
        val o1 = edges.get((p, r))
        val o2 = for (pq <- edges.get((p, q));
                      qq <- edges.get((q, q));
                      qr <- edges.get((q, r)))
                 yield CatExp(pq, CatExp(StarExp(qq), qr))
        edges += (p, r) -> OrExp(o1.getOrElse(EmptyExp), o2.getOrElse(EmptyExp)).optimized
      }
      nqs -= q
    }
    assert(nqs == Set(true, false).map(Cop2(_)))
    edges((Cop2(true), Cop2(false))).optimized
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
  val partialF: Map[Q, Set[(Concepts.Cupstar[X, Concepts.Update[Y, B]],
                            Concepts.Cupstar[Y, B])]]
) {
  import Concepts._
  implicit val updateXMonoid: Monoid[Update[X, Update[Y, B]]] = xs
  implicit val updateYMonoid: Monoid[Update[Y, B]] = ys
  val outF = partialF.withDefaultValue(Set())
  def trans(q: Q, a: A): Set[(Q, Update[X, Update[Y, B]])] = edges.withDefaultValue(Set.empty)((q, a))
  def transduce(w: List[A]): Set[List[B]] =
    Monoid.transition(Set(q0), w, trans).flatMap{ case (q, m) => outputAt(q, m).toSet }
  def outputAt(q: Q, m: Update[X, Update[Y, B]]): Set[List[B]] =
    outF(q).map{ case (alpha, beta) =>
      val updateY = Monoid.fold(erase1(flatMap1(alpha, m(_))))
      erase1(flatMap1(beta, updateY))
    }
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
      val prePost = for (y <- ys; b <- List(false, true))
        yield ((y, b) -> (if (b) List((x, y, b))
        else List((x, y, b))))
      gamma(ys)(s(x), prePost.toMap)
        .view.mapValues(_.map{ case Cop1(y) => Cop1(y); case Cop2(z) => Cop2(Cop1(z)) })
        .toMap
    }

    def embedUpdate[X, A, B](m: Update[X, B]): Update[X, Cop[A, B]] = {
      m.view.mapValues(_.map {
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
        msst.trans(q, a)
          .map { case (nextQ, mu) => {
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
    // The following algorithm can be extracted to an isolated function
    // and be used in composeNsstAndNft().
    var newStates: Set[NQ] = Set(newQ0)
    var newEdges: Map[(NQ, A), Set[(NQ, Update[Z, B])]] = Map()
    var stack = List(newQ0)
    while (stack.nonEmpty) {
      val q = stack.head
      stack = stack.tail
      for (a <- msst.in) {
        val edges = nextStates(q, a)
        newEdges += (q, a) -> edges
        val newOnes = edges.map(_._1) -- newStates
        newStates ++= newOnes
        stack = newOnes.toList ++ stack
      }
    }
    val newOutF: Map[NQ, Set[Cupstar[Z, B]]] = {
      for ((q, s) <- newStates) yield (q, s) -> msst.outF(q).map { case (alpha, beta) =>
        val m = assignFold(s, alpha)
        val assigned = beta.flatMap {
          case Cop1(y) => m(y)
          case Cop2(b) => List(Cop2(Cop2(b)))
        }
        erase1(assigned)
      }
    }
      .toMap

    new NSST[NQ, A, B, Z](
      newStates,
      msst.in,
      zs,
      newEdges,
      newQ0,
      newOutF
    )
  }
}

// The rest of this file is copy-paste from past works.
// These are just for emitting DOT graph of SSTs.
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

private class RegExp2NFA(re: RegExp[Char]) {
  private var state = -1


  private def freshState(): Int = {
    state += 1
    state
  }


  private def aux(re: RegExp[Char]): NFA[Int, Char] = re match {
    case EpsExp =>
      val q = freshState()
      new NFA(Set(q), Set(), Map(), q, Set(q))
    case EmptyExp =>
      val q = freshState()
      new NFA(Set(q), Set(), Map(), q, Set())
    case CharExp(c) =>
      val s = freshState()
      val t = freshState()
      new NFA(Set(s, t), Set(c), Map((s, Some(c)) -> Set(t)), s, Set(t))
    case OrExp(e1, e2) =>
      val n1 = aux(e1)
      val n2 = aux(e2)
      val s = freshState()
      new NFA(
        n1.states union n2.states union Set(s),
        n1.alpha union n2.alpha,
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
        n1.alpha union n2.alpha,
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
        n.alpha,
        n.transition + ((s, None) -> Set(n.q0))
          ++ n.finalStates.map(q => ((q, None), n.transition((q, None)) + s)).toMap,
        s,
        Set(n.q0)
      )
  }


  def construct(): NFA[Int, Char] = aux(re)
}
