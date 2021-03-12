package com.github.kmn4.sst.strategy

import com.github.kmn4.sst.machine.ParikhAutomaton

private case class IdentifiedPA[Q, A, L, I](id: Int, pa: ParikhAutomaton[Q, A, L, I])
