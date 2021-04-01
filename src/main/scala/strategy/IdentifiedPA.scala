package com.github.kmn4.expresso.strategy

import com.github.kmn4.expresso.machine.ParikhAutomaton

private case class IdentifiedPA[Q, A, L, I](id: Int, pa: ParikhAutomaton[Q, A, L, I])
