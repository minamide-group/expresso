package com.github.kmn4.sst

import org.scalatest.flatspec._
import scala.math.max

class TestComposition extends AnyFlatSpec {
  val nsst = NSST(
    Set(0, 1),
    Set('X', 'Y'),
    List((0, 'a', List((0, List("X:Xa", "Y:aY")))),
         (0, 'b', List((1, List("X:Xb", "Y:bY")))),
         (1, 'a', List((0, List("X:Xa", "Y:aY")))),
         (1, 'b', List((1, List("X:Xb", "Y:bY"))))),
    0,
    List((1, "XaY"))
  )
  val nft = NFT(
    Set(0, 1),
    List((0, 'a', 1, ""),
         (0, 'b', 0, "bb"),
         (1, 'a', 1, "aa"),
         (1, 'b', 0, "")),
    0,
    Set(1)
  )

  def maxTransition[Q, A, B, X](nsst: NSST[Q, A, B, X]): Int = {
    nsst.edges.foldLeft(0){ case (acc, (k, v)) => max(acc, v.size) }
  }
  "Composition" should "" in {
    val composed = NSST.composeNsstAndNft(nsst, nft)
    println(composed.states.size)
    println(maxTransition(composed))
    assert(composed.transduce("abb".toList) == Set("bbbb".toList))
  }
}
