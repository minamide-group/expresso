package com.github.kmn4.sst.experimental

import com.github.kmn4.sst.machine.ParikhAutomaton

// id 以外 sst.ParikhAutomaton と同じになって不要
case class IdentifiedPA[Q, A, L, I](id: Int, pa: ParikhAutomaton[Q, A, L, I])
