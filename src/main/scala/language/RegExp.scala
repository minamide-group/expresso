package com.github.kmn4.sst.language

import com.github.kmn4.sst._
import com.github.kmn4.sst.math._
import com.github.kmn4.sst.machine._

sealed trait RegExp[+A] {
  def usedAlphabet[B >: A]: Set[B] = this match {
    case EmptyExp | EpsExp | DotExp => Set.empty
    case CharExp(c)                 => Set(c)
    case CatExp(e1, e2)             => e1.usedAlphabet ++ e2.usedAlphabet
    case OrExp(e1, e2)              => e1.usedAlphabet ++ e2.usedAlphabet
    case StarExp(e)                 => e.usedAlphabet
    case CompExp(e)                 => e.usedAlphabet
  }

  def toNFA[B >: A](alphabet: Set[B]): NFA[Int, B] = {
    class RegExp2NFA[A](re: RegExp[A], alphabet: Set[A]) {
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
    new RegExp2NFA(this, alphabet).construct()
  }
}
case object EmptyExp extends RegExp[Nothing]
case object EpsExp extends RegExp[Nothing]
case object DotExp extends RegExp[Nothing]
case class CharExp[A, B <: A](b: B) extends RegExp[A]
case class OrExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class CatExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class StarExp[A, B <: A](b: RegExp[B]) extends RegExp[A]
case class CompExp[A, B <: A](b: RegExp[B]) extends RegExp[A]
