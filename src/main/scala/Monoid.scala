package com.github.kmn4.sst

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

  def apply[M: Monoid]: Monoid[M] = implicitly[Monoid[M]]

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
