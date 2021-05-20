package com.github.kmn4.expresso.machine

import com.github.kmn4.expresso.math._
import com.github.kmn4.expresso._

/** Nondeterministic monoid SST */
class MSST[Q, A, B, X, Y](
    val states: Set[Q],
    val in: Set[A],
    val xs: Set[X],
    val ys: Set[Y],
    val edges: MSST.Edges[Q, A, B, X, Y],
    val q0: Q,
    val partialF: Map[Q, Set[(Cupstar[X, Update[Y, B]], Cupstar[Y, B])]]
) {
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
    val (newStates, newEdges) = searchStates(Set(newQ0), msst.in)(nextStates)(
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
