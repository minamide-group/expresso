package com.github.kmn4.expresso

import com.github.kmn4.expresso.machine.{NSST}
import com.github.kmn4.expresso.math._
import org.scalatest.flatspec._
import org.scalatest.Ignore

@Ignore
class ParikhPresburgerTest extends AnyFlatSpec {
  "Calculating Parikh image" should "be done in reasonable time" in {
    // Parikh image of `nsst` should be {(a: n, b: m) | a: odd, b: non-zero even}
    val nsst = NSST(
      Set(0, 1),
      Set('X', 'Y'),
      List(
        (0, 'a', List((0, List("X:Xa", "Y:aY")))),
        (0, 'b', List((1, List("X:Xb", "Y:bY")))),
        (1, 'a', List((0, List("X:Xa", "Y:aY")))),
        (1, 'b', List((1, List("X:Xb", "Y:bY"))))
      ),
      0,
      List((1, "XaY"))
    )
    // info(s"nsst: ${nsst.presburgerFormula.smtlib}")
    val doubles = NSST(
      Set(0),
      Set('X', 'Y'),
      List((0, 'a', List((0, List("X:Xa", "Y:Ya")))), (0, 'b', List((0, List("X:Xb", "Y:Yb"))))),
      0,
      List((0, "XY"))
    )
    // info(s"doubles: ${doubles.presburgerFormula.smtlib}")
    val doublesSingle = NSST(
      Set(0),
      Set('X'),
      List((0, 'a', List((0, List("X:Xaa"))))),
      0,
      List((0, "X"))
    )
    // info(s"doublesSingle: ${doublesSingle.presburgerFormula.smtlib}")
    val append6or10 = NSST(
      Set(0),
      Set('X'),
      List((0, 'a', List((0, List("X:Xaaaaaa")), (0, List("X:Xaaaaaaaaaa"))))),
      0,
      List((0, "X"))
    )
    // info(s"append6or10: ${append6or10.presburgerFormula.smtlib}")
  }

}
