package com.github.kmn4.sst

sealed trait Cop[+A, +B] {
  def map1[C](f: A => C): Cop[C, B] = Cop.map1(this, f)
  def map2[C](f: B => C): Cop[A, C] = Cop.map2(this, f)
  def commute: Cop[B, A] = Cop.commute(this)
}
case class Cop1[A, T <: A](a: T) extends Cop[A, Nothing]
case class Cop2[B, T <: B](b: T) extends Cop[Nothing, B]
object Cop {
  def flatten[A](a: Cop[A, A]): A = a match { case Cop1(a) => a; case Cop2(a) => a }
  def map1[A, B, C](ab: Cop[A, B], f: A => C): Cop[C, B] = ab match {
    case Cop1(a) => Cop1(f(a))
    case Cop2(b) => Cop2(b)
  }
  def map2[A, B, C](ab: Cop[A, B], f: B => C): Cop[A, C] = ab match {
    case Cop1(a) => Cop1(a)
    case Cop2(b) => Cop2(f(b))
  }
  def commute[A, B](ab: Cop[A, B]): Cop[B, A] = ab match {
      case Cop1(a) => Cop2(a)
      case Cop2(b) => Cop1(b)
  }
  def flatMap1[A, B, C](ab: Cop[A, B], f: A => Cop[C, B]): Cop[C, B] = ab match {
    case Cop1(a) => f(a)
    case Cop2(b) => Cop2(b)
  }
  def flatMap2[A, B, C](ab: Cop[A, B], f: B => Cop[A, C]): Cop[A, C] = ab match {
    case Cop1(a) => Cop1(a)
    case Cop2(b) => f(b)
  }
  def erase1[A, B](ab: Cop[A, B]): Option[B] = ab match {
    case Cop1(a) => None
    case Cop2(b) => Some(b)
  }
  def erase2[A, B](ab: Cop[A, B]): Option[A] = ab match {
    case Cop1(a) => Some(a)
    case Cop2(b) => None
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
  implicit def unitMonoid = new Monoid[Unit] {
    def unit = ()
    def combine(u1: Unit, u2: Unit) = ()
  }
  implicit def vectorMonoid[K, V](
    ks: Iterable[K]
  )(implicit m: Monoid[V]): Monoid[Map[K, V]] = new Monoid[Map[K, V]] {
    def unit = Map.empty.withDefaultValue(m.unit)
    def combine(v1: Map[K, V], v2: Map[K, V]) = ks.map(k => k -> m.combine(v1(k), v2(k))).toMap
  }
  implicit val intAdditiveMonoid: Monoid[Int] = new Monoid[Int] {
    def unit = 0
    def combine(i1: Int, i2: Int) = i1 + i2
  }

  def transition[Q, A, M](
    qs: Set[Q],
    w: List[A],
    delta: (Q, A) => Set[(Q, M)]
  )(
    implicit monoid: Monoid[M]
  ): Set[(Q, M)] =
    w.foldLeft(qs.map((_, monoid.unit))){
      case (configs, a) => configs.flatMap{
        case (q, m1) => delta(q, a).map{ case (q, m2) => (q, monoid.combine(m1, m2)) }
      }
    }
  def fold[M](ms: Iterable[M])(implicit monoid : Monoid[M]): M = ms.fold(monoid.unit)(monoid.combine)
}

object Main extends App {
  val sst = new NSST[Int, Char, Char, Char](
      Set(0),
      Set('a', 'b'),
      Set('x', 'y'),
      Map(
      (0, 'a') -> Set((0, Map(
                         'x' -> List(Cop1('y'), Cop1('x')),
                         'y' -> List(Cop2('a'))
                       ))),
      (0, 'b') -> Set((0, Map(
                         'x' -> List(Cop1('y'), Cop1('x')),
                         'y' -> List(Cop2('b'))
                       )))
      ),
      0,
      Map(0 -> Set(List(Cop2('a'), Cop1('x'), Cop2('b'), Cop1('y'))))
  )
  val nft = new NFT[Int, Char, Char](
    states = Set(0, 1),
    in = Set('a', 'b'),
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
  import DOTMaker._
  println(composed.toDOT)
}
