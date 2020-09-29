package com.github.kmn4.sst

import org.scalatest.flatspec._

class TestParikhSemilinear extends AnyFlatSpec {
  "NSST.countCharOfX" should "be correct" in {
    def updateFrom(s: String): Concepts.Update[Char, Char] =
      s.split(',').map(s => {
                         val a = s.split('=')
                         val (x, alpha) = (a(0), a(1))
                         x(0) -> alpha.map(sigma => (if (sigma.isUpper) Cop1(sigma) else Cop2(sigma))).toList
                       }
      ).toMap
    val m  = updateFrom("X=Xa,Y=Ya")
    val count = NSST.countCharOfX(m)
    info(count.toString())
    info(Monoid.fold(Set('X', 'Y').map(count(_)))(Monoid.vectorMonoid(Set('a'))).toString())
  }
  "Calculating Parikh image" should "be done in reasonable time" in {
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
    info(Semilinear.toLaTeX(NSST.parikhImage(nsst)))
    val doubles = NSST(
      Set(0),
      Set('X', 'Y'),
      List((0, 'a', List((0, List("X:Xa", "Y:Ya"))))),
      0,
      List((0, "XY"))
    )
    info(s"doubles: ${Semilinear.toLaTeX(NSST.parikhImage(doubles))}")
  }
  "Calculating Parikh image of randomly generated NSST" should "be done in reasonable time" in {
    def randomNsstCustomized() = {
      val in = Set('a', 'b')
      val out = in
      val vars = Set('X', 'Y')
      val maxStates = 3
      val maxFNum = 2
      val maxRepeatB = 1
      val maxTransition = 2
      TestRandom.randomNSST(
        new TestRandom.NextState().nextState _,
        in,
        out,
        vars,
        maxStates,
        maxFNum,
        maxRepeatB,
        maxTransition
      )
    }

    for (_ <- 0 until 10) {
      val nsst = randomNsstCustomized()
      println(s"NSST states: ${nsst.states.size}\tedges: ${nsst.edges.size}")
      val start = System.nanoTime()
      def elapsed(): Long = System.nanoTime() - start
      val mnft = NSST.convertNsstToCountingNft(nsst)
      println(s"${elapsed()}: Converted to MNFT: ${mnft.states.size} states, ${mnft.edges.size} edges")
      val regex = MNFT.outputRegex(mnft)
      println(s"${elapsed()}: Converted to Regex: ${regex.size}")
      if (regex.size < 10000) println(regex)
      val s = Semilinear.fromRegex(regex)(Monoid.vectorMonoid(nsst.out)(Monoid.intAdditiveMonoid))
      println(s"${elapsed()}: Converted to Semilinear")
      println(s"${Semilinear.toLaTeX(s)}")
    }
  }

}
