package com.github.kmn4.sst.experimental

import com.github.kmn4.sst.ParikhSST
import com.github.kmn4.sst.Presburger
import com.github.kmn4.sst

// id 以外 sst.ParikhAutomaton と同じになって不要
case class IdentifiedPA[Q, A, L, I](
    id: Int,
    pa: sst.ParikhAutomaton[Q, A, L, I]
)
