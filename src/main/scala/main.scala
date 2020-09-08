package com.github.kmn4.sst

trait Cop[A, B]
case class Cop1[A, B](a: A) extends Cop[A, B]
case class Cop2[A, B](b: B) extends Cop[A, B]
object Cop {
  def flatMap1[A, B](l: List[Cop[A, B]], f: A => List[Cop[A, B]]): List[Cop[A, B]] =
    l.flatMap{
      case Cop1(a) => f(a)
      case Cop2(b) => List(Cop2(b))
    }
  def flatMap2[A, B](l: List[Cop[A, B]], f: B => List[Cop[A, B]]): List[Cop[A, B]] =
    l.flatMap{
      case Cop1(a) => List(Cop1(a))
      case Cop2(b) => f(b)
    }
  def erase1[A, B](l: List[Cop[A, B]]): List[B] = l.flatMap{
    case Cop1(a) => Nil
    case Cop2(b) => List(b)
  }
  def erase2[A, B](l: List[Cop[A, B]]): List[A] = l.flatMap{
    case Cop1(a) => List(a)
    case Cop2(b) => Nil
  }
}

trait Monoid[M] {
  def unit: M
  def combine(m1: M, m2: M): M
}

object Monoid {
  implicit def listMonoid[A] = new Monoid[List[A]] {
    def unit = Nil
    def combine(l1: List[A], l2: List[A]) = l1 ++ l2
  }
  def transition[Q, A, M](
    q: Q,
    w: List[A],
    delta: (Q, A) => Set[(Q, M)]
  )(
    implicit monoid: Monoid[M]
  ): Set[(Q, M)] =
    w.foldLeft(Set((q, monoid.unit))){
      case (configs, a) => configs.flatMap{
        case (q, m1) => delta(q, a).map{ case (q, m2) => (q, monoid.combine(m1, m2)) }
      }
    }
}

class NSST[Q, A, B, X](
  val states: Set[Q],
  val in: Set[A],
  val out: Set[B],
  val variables: Set[X],
  val edges: NSST.Edges[Q, A, X, B],
  val q0: Q,
  val outF: NSST.Output[Q, X, B]
) {
  import NSST._
  implicit val monoid: Monoid[Update[X, B]] = variables
  def trans(q: Q, a: A): Set[(Q, Update[X, B])] = edges.withDefaultValue(Set.empty)((q, a))
  def transduce(w: List[A]): Set[List[B]] =
    Monoid.transition(q0, w, trans).flatMap{ case (q, m) => outputAt(q, m).toSet }
  def outputAt(q: Q, m: Update[X, B]): Option[List[B]] =
    outF.get(q).map { Cop.flatMap1(_, m) }.map { eraseVar }
}

object NSST {
  type Update[X, B] = Map[X, List[Cop[X, B]]]
  type Edges[Q, A, X, B] = Map[(Q, A), Set[(Q, Update[X, B])]]
  type Output[Q, X, B] = Map[Q, List[Cop[X, B]]]
  implicit def updateMonoid[X, B](xs: Iterable[X]): Monoid[Update[X, B]] = new Monoid[Update[X, B]] {
    def combine(m1: Update[X, B], m2: Update[X, B]): Update[X, B] =
      for ((k, v) <- m2) yield (k -> Cop.flatMap1(v, m1(_)))
    def unit: Update[X, B] = Map.from(xs.map(x => x -> List(Cop1[X, B](x))))
  }
  def eraseVar[X, B](l: List[Cop[X, B]]): List[B] = Cop.erase1(l)

  // Type of states of composed NSST without initial one.
  type ComposedQ[Q1, Q2, X] = (Q1, Map[X, (Q2, Q2)])
  def composeNsstAndNft[A, B, C, Q1, X, Q2](
    nsst: NSST[Q1, A, B, X],
    nft: NFT[Q2, B, C]
  ): NSST[Option[ComposedQ[Q1, Q2, X]], A, C, X] = {
    type NoOp = ComposedQ[Q1, Q2, X]
    type NewQ = Option[NoOp]

    def transitionWith(kt: Map[X, (Q2, Q2)])(q: Q2, w: List[Cop[X, B]]) = {
      def transWithKT(q: Q2, sigma: Cop[X, B]): Set[(Q2, List[Cop[X, C]])] = sigma match {
        case Cop1(x) => kt.get(x).flatMap{
          case (k, t) => if (q == k) Some((t, List(Cop1[X, C](x)))) else None
        }.toSet
        case Cop2(a) => nft.trans(q, a).map{ case (q, w) => (q, w.map(Cop2(_))) }
      }
      Monoid.transition(q, w, transWithKT)
    }

    val ktList: List[Map[X, (Q2, Q2)]] = {
      val q2pair = (for (q21 <- nft.states;
                         q22 <- nft.states)
                    yield Some((q21, q22)))
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

    def nextStates(q: NoOp, a: A): Set[(NoOp, Update[X, C])] = {
      val (q1, kt) = q
      val got =
      for ((q1p, m1) <- nsst.trans(q1, a);
           ktp <- ktList
           if nsst.variables.forall(x =>
               { // Condition 1
                 val vars = Cop.erase2(m1(x)).toSet
                 vars.isEmpty || !(vars subsetOf kt.keySet) || (kt.keySet contains x) }))
      yield {
        // Enumerate possible variable updates with (q1p, ktp) as a next state.
        val dom = ktp.keySet
        val (inKT, notInKT) = nsst.variables.partition(dom contains _)
        // mxSet(x) := A set of possible values of m(x).
        var mxSet: Map[X, Set[List[Cop[X, C]]]] =
          Map.from(notInKT.map(x => x -> Set(List(Cop1(x)))))
        val trans = transitionWith(kt) _
        mxSet ++= (for (x <- inKT) yield {
                  val s = (for ((q2, mx) <- trans(ktp(x)._1, m1(x))
                                // If the folloing conditions is not met,
                                // then ms(x) is empty and thus cannot transition
                                // from q to (q1p, ktp) by a.
                                if q2 == ktp(x)._2)
                           yield mx)
                  x -> s
                })
        val mxList = mxSet.map{ case (x, s) => (x, s.toList) }
        val variables = nsst.variables.toList
        def product[T](ls: List[List[T]]): List[List[T]] = ls match {
          case Nil => List(Nil)
          case l :: ls => {
            for (e <- l;
                 p <- product(ls))
            yield e :: p
          }
        }
        val mList = product(variables.map(mxList(_)))
        val ms = mList.map(m => (variables zip m).toMap).toSet
        ms.map(((q1p, ktp), _))
      }
      got.flatten
    }

    def nextStatesNewQ(q: NewQ, a: A): Set[(NewQ, Update[X, C])] = q match {
      case Some(q) => nextStates(q, a).map{ case (q, m) => (Some(q), m) }
      case None => {
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
    new NSST(
      newStates,
      nsst.in,
      nft.out,
      nsst.variables,
      newEdges,
      None,
      newOutF
    )
  }
  // End of composeNsstAndNft
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
}

object Main extends App {
  val sst = new NSST[Int, Char, Char, Char](
    states = Set(0),
    in = Set('a', 'b'),
    out = Set('a', 'b'),
    variables = Set('x', 'y'),
    edges = Map(
      (0, 'a') -> Set((0, Map(
                         'x' -> List(Cop1('y'), Cop1('x')),
                         'y' -> List(Cop2('a'))
                       ))),
      (0, 'b') -> Set((0, Map(
                         'x' -> List(Cop1('y'), Cop1('x')),
                         'y' -> List(Cop2('b'))
                       )))
    ),
    q0 = 0,
    outF = Map(0 -> List(Cop2('a'), Cop1('x'), Cop2('b'), Cop1('y')))
  )
  val nft = new NFT[Int, Char, Char](
    states = Set(0, 1),
    in = Set('a', 'b'),
    out = Set('a', 'b'),
    edges = Map(
      (0, 'a') -> Set((1, List())),
      (0, 'b') -> Set((0, List('b', 'b'))),
      (1, 'a') -> Set((1, List('a', 'a'))),
      (1, 'b') -> Set((0, List()))
    ),
    q0 = 0,
    finals = Set(1)
  )
  println(sst.transduce(List('b','a', 'b', 'a')))
  println(nft.transduce(List('a', 'a', 'b', 'b', 'a')))
  val composed = NSST.composeNsstAndNft(sst, nft)
  println(composed.states.size)
  println(composed.transduce(List('b','a', 'b', 'a')))
}
