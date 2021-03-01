package com.github.kmn4.sst.experimental

import com.github.kmn4.sst.ParikhSST
import com.github.kmn4.sst.Presburger

case class ParikhAutomaton[Q, A, L, I](
    id: Int,
    states: Set[Q],
    inSet: Set[A],
    ls: Set[L],
    is: Set[I],
    edges: Set[(Q, A, ParikhSST.ParikhUpdate[L], Q)],
    q0: Q,
    acceptRelation: (Q, Map[L, Int]), // ここがシングルトン
    acceptFormulas: Formulas[I, L]
)
