package com.github.kmn4.sst

sealed trait Log

case class CompositionLog(
    times: CompositionLog.Times,
    sizes: CompositionLog.Sizes
) extends Log {
  override def toString(): String = {
    def toMillis(n: Long) = n / 1000000
    val beforeRemove = sizes.backward.statesSize
    val afterRemove = sizes.unreachables.reachablesSize
    s"""Composition of ...
\tComposition took\t${toMillis(times.redundantVars-times.start)} ms
\tDetailed elapsed time:
\t\tBackward state exploration\t${toMillis(times.backward-times.start)} ms
\t\tRemoving unreachable\t${toMillis(times.unreachables-times.backward)} ms
\t\tMSST construction (overall)\t${toMillis(times.msst-times.start)} ms
\t\tNSST construction (overall)\t${toMillis(times.nsst-times.start)} ms
\t\tRemoving redundant variables\t${toMillis(times.redundantVars-times.nsst)} ms
\tSizes of intermidiate products:
\t\tStates\t${beforeRemove} -> ${afterRemove} (${afterRemove.toDouble / beforeRemove.toDouble})"""
  }
}

object CompositionLog {
  case class Times(
      start: Long = 0,
      backward: Long = 0,
      unreachables: Long = 0,
      msst: Long = 0,
      nsst: Long = 0,
      redundantVars: Long = 0
  )
  case class BackwardFinished(
      statesSize: Int = 0,
      edgesSize: Int = 0,
      edgesNorm: Int = 0,
      initialStatesSize: Int = 0
  )
  case class UnreachablesRemoved(reachablesSize: Int = 0)
  case class Sizes(
      backward: BackwardFinished = BackwardFinished(),
      unreachables: UnreachablesRemoved = UnreachablesRemoved()
  )
}

class CompositionLogger {
  import CompositionLog._
  var times = Times()
  var sizes = Sizes()

  def start() = {
    times = Times(start=System.nanoTime())
    sizes = Sizes()
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
  }

  def log: CompositionLog = CompositionLog(times, sizes)
}
