package com.github.kmn4.sst.experimental

import com.github.kmn4.sst.ParikhSST
import com.github.kmn4.sst.Presburger

// id 以外 sst.ParikhAutomaton と同じになって不要
case class ParikhAutomaton[Q, A, L, I](
    id: Int,
    states: Set[Q],
    inSet: Set[A],
    ls: Set[L],
    is: Set[I],
    edges: Set[(Q, A, ParikhSST.ParikhUpdate[L], Q)],
    q0: Q,
    acceptRelation: (Q, Map[L, Int]), // FIXME ここの縛りをなくす
    acceptFormulas: Formulas[I, L]
)
