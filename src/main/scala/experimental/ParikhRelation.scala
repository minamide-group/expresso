package com.github.kmn4.sst.experimental

import com.github.kmn4.sst.Presburger

case class ParikhRelation[Q, A, L, I](
    parikhAutomata: Seq[Seq[(ParikhAutomaton[Q, A, L, I], Int)]],
    globalFormulas: Seq[Presburger.Formula[I]]
)
