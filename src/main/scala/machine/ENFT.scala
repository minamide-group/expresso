package com.github.kmn4.expresso.machine

import com.github.kmn4.expresso.graphToMap
import com.github.kmn4.expresso.math.Monoid

/** Monoid NFT with epsilon transition.
  * Inital state and final state of this class Must be singleton.
  */
case class ENFT[Q, A, M: Monoid](
    val states: Set[Q],
    val in: Set[A],
    val edges: Set[(Q, Option[A], M, Q)],
    val initial: Q,
    val finalState: Q
) {
  val trans = graphToMap(edges) { case (q, a, m, r) => (q, a) -> (r, m) }
  def renamed: ENFT[Int, A, M] = {
    val stateMap = (states zip LazyList.from(0)).toMap
    val newEdges = edges.map { case (q, a, m, r) => (stateMap(q), a, m, stateMap(r)) }
    new ENFT(
      stateMap.map(_._2).toSet,
      in,
      newEdges,
      stateMap(initial),
      stateMap(finalState)
    )
  }

  /** Returns an input by which the machine cat output `wanted`.
    * If configuration has `m` of `M` and `prune(m)` is `true`,
    * then that search branch is teminated. */
  def takeInputFor(wanted: M, prune: M => Boolean): List[A] = {
    val inSetEps = List.from(in.map(Option.apply) + None)
    val queue = collection.mutable.Queue[(Q, List[A], M)]((initial, Nil, Monoid[M].unit))
    var visited: Set[(Q, M)] = queue.view.map { case (q, _, m) => (q, m) }.toSet
    def terminate(q: Q, m: M): Boolean = prune(m) || visited((q, m))
    while (queue.nonEmpty) {
      val (q, as1, m1) = queue.dequeue()
      if (q == finalState && m1 == wanted) return as1.reverse
      val added = {
        inSetEps.flatMap(o =>
          trans((q, o)).flatMap {
            case (q, m2) => {
              val as = o match {
                case None    => as1
                case Some(a) => a :: as1
              }
              val m = Monoid[M].combine(m1, m2)
              if (terminate(q, m)) Set.empty
              else Set((q, as, m))
            }
          }
        )
      }
      for ((q, _, m) <- added) visited += ((q, m))
      queue ++= added
    }
    throw new Exception("No input string gives wanted thing.")
  }
}
