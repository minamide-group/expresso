package com.github.kmn4.expresso.machine

import com.github.kmn4.expresso._
import com.github.kmn4.expresso.math._

class DFA[Q, A](
    val states: Set[Q],
    val alpha: Set[A],
    val transition: Map[(Q, A), Q],
    val q0: Q,
    val finalStates: Set[Q]
) {

  def trans(q: Q, w: List[A]): Q =
    w match {
      case Nil    => q
      case a :: w => trans(transition(q, a), w)
    }

  def accept(w: List[A]): Boolean =
    try finalStates.contains(trans(q0, w))
    catch {
      case e: NoSuchElementException => false
    }

  lazy val edges: Set[(Q, A, Q)] = for {
    q <- states
    a <- alpha
    r <- transition.get((q, a))
  } yield (q, a, r)

  def reversed: DFA[Int, A] = {
    val revMap = graphToMap(edges) { case (q, a, r) => (r, a) -> q }
    val (newStates, newEdges) = searchStates(Set(finalStates), alpha) {
      case (qs, a) =>
        val rs = qs.flatMap(q => revMap((q, a)))
        Iterable(rs)
    }(identity, { case (qs, a, rs) => (qs, a, rs) })
    val newEdgeMap =
      newEdges.iterator.map { case (q, a, r) => (q, a) -> r }.toMap[(Set[Q], A), Set[Q]]
    new DFA(
      newStates,
      alpha,
      newEdgeMap,
      finalStates,
      newStates.filter(_ contains q0)
    ).renamed
  }

  def minimized: DFA[Int, A] = reversed.reversed

  def asNFA: NFA[Q, A] = new NFA(
    states,
    alpha,
    transition.map({ case ((p, a), q) => ((p, Some(a)), Set(q)) }).toMap,
    q0,
    finalStates
  )

  def renamed: DFA[Int, A] = {
    val stateMap = (states zip LazyList.from(0)).toMap
    new DFA(
      stateMap.values.toSet,
      alpha,
      transition.map { case ((p, a), q) => (stateMap(p), a) -> stateMap(q) }.toMap,
      stateMap(q0),
      finalStates.map(stateMap)
    )
  }

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

  def toParikhAutomaton[L, I]: ParikhAutomaton[Q, A, L, I] = ParikhAutomaton(
    states,
    alpha,
    Set.empty,
    Set.empty,
    transition.map { case ((q, a), r) => (q, a, Map.empty[L, Int], r) }.toSet,
    q0,
    finalStates.map((_, Map.empty)),
    Seq.empty
  )

  def toIdentityNSST: NSST[Q, A, A, Unit] = NSST(
    states,
    alpha,
    Set(()),
    transition.map { case ((q, a), r) => (q, a, Map(() -> List(Cop1(()), Cop2(a))), r) }.toSet,
    q0,
    finalStates.map(q => q -> Set(List[Cop[Unit, A]](Cop1(())))).toMap
  )
}

object DFA {
  def universal[Q, A](q: Q, inSet: Set[A]): DFA[Q, A] = new DFA(
    Set(q),
    inSet,
    inSet.map((q, _) -> q).toMap,
    q,
    Set(q)
  )
}

class NFA[Q, A](
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
