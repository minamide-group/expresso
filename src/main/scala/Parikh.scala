package com.github.kmn4.sst

import com.microsoft.z3
import Presburger._

sealed trait RegExp[+A]
case object EmptyExp extends RegExp[Nothing]
case object EpsExp extends RegExp[Nothing]
case object DotExp extends RegExp[Nothing]
case class CharExp[A, B <: A](b: B) extends RegExp[A]
case class OrExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class CatExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class StarExp[A, B <: A](b: RegExp[B]) extends RegExp[A]
case class CompExp[A, B <: A](b: RegExp[B]) extends RegExp[A]

object Parikh {
  type Image[A] = Map[A, Int]
  sealed trait EnftVar[Q, B, E]
  case class BNum[Q, B, E](b: B) extends EnftVar[Q, B, E]
  case class ENum[Q, B, E](e: E) extends EnftVar[Q, B, E]
  case class Dist[Q, B, E](q: Q) extends EnftVar[Q, B, E]
  // case class IsInit[Q, B, E](q: Q) extends EnftVar[Q, B,E]
  // case class IsFin[Q, B, E](q: Q) extends EnftVar[Q, B,E]
  def parikhEnftToPresburgerFormula[Q, A, B](
      enft: ENFT[Q, A, Image[B]]
  ): Formula[EnftVar[Q, B, (Q, Image[B], Q)]] = {
    type Edge = (Q, Image[B], Q)
    type X = EnftVar[Q, B, Edge]
    val states = enft.states.toSeq
    val edges: Seq[Edge] = {
      for (((q, a), s) <- enft.edges; (r, v) <- s)
        yield (q, v, r)
    } // Needed to exclude duplicate.
    .toSet.toList
    val edgesFrom: Map[Q, Seq[Edge]] = edges.groupBy(_._1).withDefaultValue(Seq.empty)
    val edgesTo: Map[Q, Seq[Edge]] = edges.groupBy(_._3).withDefaultValue(Seq.empty)
    val input: Map[Q, Term[X]] = states
      .map(q =>
        q ->
          Add[X](
            edgesTo(q)
              .map[Term[X]](e => Var(ENum(e)))
              .appended(
                if (q == enft.initial) Const(1) else Const(0)
              )
          )
      )
      .toMap
    val output: Map[Q, Term[X]] = states
      .map(q =>
        q ->
          Add[X](
            edgesFrom(q)
              .map[Term[X]](e => Var(ENum(e)))
              .appended(
                if (q == enft.finalState) Const(1) else Const(0)
              )
          )
      )
      .toMap
    val euler: Formula[X] = {
      val clauses = states.map(q => Eq(Sub(input(q), output(q)), Const(0)))
      // `caluses` cannot be empty bacause MNFT has at least one state.
      Conj(clauses)
    }
    val connectivity: Formula[X] = {
      val clauses =
        states.map(q => {
          val unreachable = Conj[X](Seq(Eq(Var(Dist(q)), Const(-1)), Eq(output(q), Const(0))))
          val reachable = {
            val isInit: Formula[X] =
              if (q == enft.initial) Eq(Var(Dist(q)), Const(0))
              else Bot()
            val reachedFromSomewhere = edgesTo(q).map(e => {
              val (p, v, _) = e
              Conj(
                List[Formula[X]](
                  Eq(Var(Dist(q)), Add(Seq(Var(Dist(p)), Const(1)))),
                  Gt(Var(ENum(e)), Const(0)),
                  Ge(Var(Dist(p)), Const(0))
                )
              )
            })
            Disj(reachedFromSomewhere.appended(isInit))
          }
          Disj(Seq(unreachable, reachable))
        })
      Conj(clauses)
    }
    val bs = edges.foldLeft[Set[B]](Set.empty) { case (acc, (_, v, _)) => acc union v.keySet }
    val parikh: Formula[X] = {
      val clauses = bs.toSeq.map[Formula[X]](b => {
        val sum: Term[X] = Add(
          edges.map[Term[X]] {
            case (q, v, r) => Mult(Const(v.getOrElse(b, 0)), Var(ENum((q, v, r))))
          }
        )
        Eq(Var(BNum(b)), sum)
      })
      Conj(clauses)
    }
    val boundedVars: Seq[X] = states.map[X](q => Dist(q)) ++ edges.map(e => ENum(e))
    val vars: Seq[X] = boundedVars ++ bs.map(BNum.apply)
    val positive: Formula[X] = Conj(
      vars.map[Formula[X]] {
        case BNum(b) => Ge(Var(BNum(b)), Const(0))
        case ENum(e) => Ge(Var(ENum(e)), Const(0))
        case Dist(q) => Ge(Var(Dist(q)), Const(-1))
      }
    )
    val conj: Formula[X] = Conj(List(euler, connectivity, parikh, positive))
    Exists(boundedVars.map(Var.apply), conj)
  }
}
