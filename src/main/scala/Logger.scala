package com.github.kmn4.sst

import com.github.kmn4.sst.machine.{NSST, MSST}

trait CompositionLogger {
  def start[Q1, Q2, A, B, C, X, Y](n1: NSST[Q1, A, B, X], n2: NSST[Q2, B, C, Y]): Unit
  def invTransX[Q1, Q2, X](m: Map[Q1, Map[(Q2, X), Set[Q2]]]): Unit
  def backwardFinished[Q, A, M](states: Set[Q], edges: Iterable[(Q, A, M, Q)], initialStates: Set[Q]): Unit
  def unreachablesRemoved[Q](reachables: Set[Q]): Unit
  def msstConstructed[Q, A, C, X, Y](msst: MSST[Q, A, C, X, Y]): Unit
  def nsstConstructed[Q, A, C, Z](nsst: NSST[Q, A, C, Z]): Unit
  def redundantVarsRemoved[Q, A, C, Z](result: NSST[Q, A, C, Z]): Unit
}

object NopLogger extends CompositionLogger {
  def start[Q1, Q2, A, B, C, X, Y](n1: NSST[Q1, A, B, X], n2: NSST[Q2, B, C, Y]): Unit = {}
  def invTransX[Q1, Q2, X](m: Map[Q1, Map[(Q2, X), Set[Q2]]]): Unit = {}
  def backwardFinished[Q, A, M](
      states: Set[Q],
      edges: Iterable[(Q, A, M, Q)],
      initialStates: Set[Q]
  ): Unit = {}
  def unreachablesRemoved[Q](reachables: Set[Q]): Unit = {}
  def msstConstructed[Q, A, C, X, Y](msst: MSST[Q, A, C, X, Y]): Unit = {}
  def nsstConstructed[Q, A, C, Z](nsst: NSST[Q, A, C, Z]): Unit = {}
  def redundantVarsRemoved[Q, A, C, Z](result: NSST[Q, A, C, Z]): Unit = {}
}

sealed trait Log

case class CompositionLog(
    times: CompositionLog.Times,
    sizes: CompositionLog.Sizes
) extends Log {
  override def toString(): String = {
    def toMillis(n: Long) = n / 1000000
    val beforeRemove = sizes.backward.statesSize
    val afterRemove = sizes.unreachables.reachablesSize
    s"""---
Composition ingredients:
\t1:\t${sizes.started.first}
\t2:\t${sizes.started.second}
Composition took\t${toMillis(times.redundantVars - times.start)} ms
Detailed elapsed time:
\tBackward reachability analysis\t${toMillis(times.invTrans - times.start)} ms
\tBackward state exploration\t${toMillis(times.backward - times.start)} ms
\tRemoving unreachable\t${toMillis(times.unreachables - times.backward)} ms
\tMSST construction (overall)\t${toMillis(times.msst - times.start)} ms
\tNSST construction (overall)\t${toMillis(times.nsst - times.start)} ms
\tRemoving redundant variables\t${toMillis(times.redundantVars - times.nsst)} ms
Sizes of intermidiate products:
\tStates\t${beforeRemove} -> ${afterRemove} (${afterRemove.toDouble / beforeRemove.toDouble})
Resulting SST:\t${sizes.finished}"""
  }
}

object CompositionLog {
  case class Times(
      start: Long = 0,
      invTrans: Long = 0,
      backward: Long = 0,
      unreachables: Long = 0,
      msst: Long = 0,
      nsst: Long = 0,
      redundantVars: Long = 0
  )
  case class NsstSummary(
      statesSize: Int = 0,
      varsSize: Int = 0,
      edgesSize: Int = 0,
      edgesNorm: Int = 0,
      fSize: Int = 0,
      fNorm: Int = 0
  )
  object NsstSummary {
    def apply[Q, A, B, X](n: NSST[Q, A, B, X]): NsstSummary = NsstSummary(
      statesSize = n.states.size,
      varsSize = n.variables.size,
      edgesSize = n.edges.size,
      edgesNorm = n.delta.view.map(_._2.size).fold(0)(scala.math.max),
      fSize = n.outF.size,
      fNorm = n.outF.view.map(_._2.size).fold(0)(scala.math.max)
    )
  }
  case class Started(
      first: NsstSummary = NsstSummary(),
      second: NsstSummary = NsstSummary()
  )
  case class BackwardFinished(
      statesSize: Int = 0,
      edgesSize: Int = 0,
      edgesNorm: Int = 0,
      initialStatesSize: Int = 0
  )
  case class UnreachablesRemoved(reachablesSize: Int = 0)
  case class Sizes(
      started: Started = Started(),
      backward: BackwardFinished = BackwardFinished(),
      unreachables: UnreachablesRemoved = UnreachablesRemoved(),
      finished: NsstSummary = NsstSummary()
  )
}
class BufferedLogger extends CompositionLogger {
  import CompositionLog._
  var times = Times()
  var sizes = Sizes()
  var logs: List[CompositionLog] = Nil

  def start[Q1, Q2, A, B, C, X, Y](n1: NSST[Q1, A, B, X], n2: NSST[Q2, B, C, Y]): Unit = {
    times = Times(start = System.nanoTime())
    sizes = Sizes(started = Started(first = NsstSummary(n1), second = NsstSummary(n2)))
  }

  def invTransX[Q1, Q2, X](m: Map[Q1, Map[(Q2, X), Set[Q2]]]): Unit = {
    times = times.copy(invTrans = System.nanoTime())
  }

  def backwardFinished[Q, A, M](states: Set[Q], edges: Iterable[(Q, A, M, Q)], initialStates: Set[Q]) = {
    times = times.copy(backward = System.nanoTime())
    sizes = sizes.copy(backward =
      sizes.backward
        .copy(statesSize = states.size, edgesSize = edges.size, initialStatesSize = initialStates.size)
    )
  }

  def unreachablesRemoved[Q](reachables: Set[Q]) = {
    times = times.copy(unreachables = System.nanoTime())
    sizes = sizes.copy(unreachables = sizes.unreachables.copy(reachablesSize = reachables.size))
  }

  def msstConstructed[Q, A, C, X, Y](msst: MSST[Q, A, C, X, Y]) = {
    times = times.copy(msst = System.nanoTime())
  }

  def nsstConstructed[Q, A, C, Z](nsst: NSST[Q, A, C, Z]) = {
    times = times.copy(nsst = System.nanoTime())
  }

  def redundantVarsRemoved[Q, A, C, Z](result: NSST[Q, A, C, Z]) = {
    times = times.copy(redundantVars = System.nanoTime())
    sizes = sizes.copy(finished = NsstSummary(result))
    logs = logs ++ List(CompositionLog(times, sizes))
  }

  def flush: Unit = println(flushString)
  def flushString: String = logs.mkString("\n")
}
