package com.github.kmn4

import scala.collection.immutable.Queue

package object sst {

  type Cupstar[X, B] = List[Cop[X, B]]
  type Update[X, B] = Map[X, Cupstar[X, B]]
  def flatMap1[A, B, C](abs: Cupstar[A, B], f: A => Cupstar[C, B]): Cupstar[C, B] =
    abs.flatMap { case Cop1(a) => f(a); case Cop2(b) => List(Cop2(b)) }
  def erase1[A, B](abs: Cupstar[A, B]): List[B] = abs.flatMap(Cop.erase1(_))
  def erase2[A, B](abs: Cupstar[A, B]): List[A] = abs.flatMap(Cop.erase2(_))
  def varsIn[X, A](xas: Cupstar[X, A]): Set[X] = erase2(xas).toSet
  def charsIn[X, A](xas: Cupstar[X, A]): Set[A] = erase1(xas).toSet
  def charsIn[X, A](m: Update[X, A]): Set[A] = m.flatMap { case (_, xas) => charsIn(xas) }.toSet
  implicit def updateMonoid[X, B](xs: Iterable[X]): Monoid[Update[X, B]] =
    new Monoid[Update[X, B]] {
      def combine(m1: Update[X, B], m2: Update[X, B]): Update[X, B] = Map.from {
        for (x <- xs) yield (x -> flatMap1(m2(x), m1(_)))
      }
      // Some codes assume that updates contain definition for all variables,
      // so cannot use `Map.empty.withDefault(x => x -> List(Cop1(x)))` as `unit`.
      def unit: Update[X, B] = Map.from(xs.map(x => x -> List(Cop1(x))))
    }

  def closure[Q](start: Set[Q], edges: Q => Set[Q]): Set[Q] = {
    def trans(qs: Set[Q]): Set[Q] =
      qs.foldLeft(Set.empty[Q]) { case (acc, q) => acc union edges(q) }
    var newQs = start
    var clos = start
    while (newQs.nonEmpty) {
      newQs = trans(newQs) -- clos
      clos ++= newQs
    }
    clos
  }

  def searchStates[Q, A, C, E](
      baseStates: Set[Q],
      inSet: Set[A]
  )(nextConfigs: (Q, A) => Iterable[C])(toState: C => Q, toEdge: (Q, A, C) => E): (Set[Q], Set[E]) = {
    val states = collection.mutable.Set.from(baseStates)
    var edges: List[E] = Nil
    var stack: List[Q] = states.toList
    while (stack.nonEmpty) {
      val h = stack.head
      stack = stack.tail
      for {
        a <- inSet
        c <- nextConfigs(h, a)
      } {
        edges ::= toEdge(h, a, c)
        val q = toState(c)
        if (states.add(q)) {
          stack ::= q
        }
      }
    }
    (states.toSet, edges.toSet)
  }

  /** Breadth-first search for an input by which given system can transition to final state. */
  def transitionSystemBFS[Q, A](
      states: Set[Q],
      in: Iterable[A],
      trans: (Q, A) => Set[Q],
      q0: Q,
      finals: Set[Q]
  ): List[A] = {
    var visited: Set[Q] = Set.empty
    var toVisit: Queue[(Q, List[A])] = Queue((q0, Nil))
    while (toVisit.nonEmpty) {
      val (q, as) = toVisit.head
      toVisit = toVisit.tail
      if (finals contains q) return as.reverse
      val fromQ = in.flatMap(a => trans(q, a).map((_, a :: as))).toSet
      val notVisited = fromQ.filterNot(visited contains _._1)
      visited ++= notVisited.map(_._1)
      toVisit = toVisit.appendedAll(notVisited)
    }
    throw new Exception("Given system is empty.")
  }

}
