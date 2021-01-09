package com.github.kmn4.sst

import com.microsoft.z3

import Presburger._

object Parikh {
  type Image[A] = Map[A, Int]
  sealed trait EnftVar[Q, B, E]
  case class BNum[Q, B, E](b: B) extends EnftVar[Q, B, E] // number of occurrence of output symbol b
  case class EdgeNum[Q, B, E](e: E) extends EnftVar[Q, B, E] // number of occurrence of edge e
  case class Distance[Q, B, E](q: Q) extends EnftVar[Q, B, E] // distance from initial state to q
  def parikhEnftToPresburgerFormula[Q, A, B](
      enft: ENFT[Q, A, Image[B]]
  ): Formula[EnftVar[Q, B, (Q, Image[B], Q)]] = {
    type Edge = (Q, Image[B], Q)
    type X = EnftVar[Q, B, Edge]
    val states = enft.states.toSeq
    val edges: Seq[Edge] = enft.edges.map { case (q, _, m, r) => (q, m, r) }.toSeq
    val edgesFrom: Map[Q, Seq[Edge]] = edges.groupBy(_._1).withDefaultValue(Seq.empty)
    val edgesTo: Map[Q, Seq[Edge]] = edges.groupBy(_._3).withDefaultValue(Seq.empty)
    val input: Map[Q, Term[X]] = states
      .map(q =>
        q ->
          Add[X](
            edgesTo(q)
              .map[Term[X]](e => Var(EdgeNum(e)))
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
              .map[Term[X]](e => Var(EdgeNum(e)))
              .appended(
                if (q == enft.finalState) Const(1) else Const(0)
              )
          )
      )
      .toMap
    val euler: Formula[X] = {
      val clauses = states.map(q => Eq(input(q), output(q)))
      // `caluses` cannot be empty bacause ENFT has at least two state.
      Conj(clauses)
    }
    val connectivity: Formula[X] = {
      val clauses =
        states.map(q => {
          val unreachable = Conj[X](Seq(Eq(Var(Distance(q)), Const(-1)), Eq(output(q), Const(0))))
          val reachable = {
            val isInit: Formula[X] = if (q == enft.initial) Eq(Var(Distance(q)), Const(0)) else Bot()
            val reachedFromSomewhere = edgesTo(q).map {
              case e @ (p, v, _) => {
                Conj(
                  Seq[Formula[X]](
                    Eq(Var(Distance(q)), Add(Seq(Var(Distance(p)), Const(1)))),
                    Gt(Var(EdgeNum(e)), Const(0)),
                    Ge(Var(Distance(p)), Const(0))
                  )
                )
              }
            }
            Disj(isInit +: reachedFromSomewhere)
          }
          Disj(Seq(unreachable, reachable))
        })
      Conj(clauses)
    }
    val bs = edges.foldLeft[Set[B]](Set.empty) { case (acc, (_, v, _)) => acc union v.keySet }
    val parikh: Formula[X] = {
      val clauses = bs.toSeq.map[Formula[X]](b => {
        val bNums = edges.map[Term[X]] {
          case e @ (q, v, r) => Mult(Const(v.getOrElse(b, 0)), Var(EdgeNum(e)))
        }
        val sum: Term[X] = Add(bNums)
        Eq(Var(BNum(b)), sum)
      })
      Conj(clauses)
    }
    val boundedVars: Seq[X] = states.map[X](q => Distance(q)) ++ edges.map(e => EdgeNum(e))
    val vars: Seq[X] = boundedVars ++ bs.map(BNum.apply)
    val positive: Formula[X] = Conj(
      vars.map[Formula[X]] {
        case BNum(b)     => Ge(Var(BNum(b)), Const(0))
        case EdgeNum(e)  => Ge(Var(EdgeNum(e)), Const(0))
        case Distance(q) => Ge(Var(Distance(q)), Const(-1))
      }
    )
    val conj: Formula[X] = Conj(Seq(euler, connectivity, parikh, positive))
    Exists(boundedVars.map(Var.apply), conj)
  }
}
