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
  implicit def unitMonoid = new Monoid[Unit] {
    def unit = ()
    def combine(u1: Unit, u2: Unit) = ()
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
    partialF = Map(0 -> Set(List(Cop2('a'), Cop1('x'), Cop2('b'), Cop1('y'))))
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
  import DOTMaker._
  println(composed.toDOT)
}
