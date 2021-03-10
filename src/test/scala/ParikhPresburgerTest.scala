package com.github.kmn4.sst

import com.github.kmn4.sst.machine.{NSST}
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

  "Found bug" should "be fixed" in {
    import scala.collection.immutable.{HashMap, HashSet}
    import com.microsoft.z3
    val List(a, b, x, y) = "abxy".toList
    val n = NSST[Int, Char, Char, Char](
      states = Set(1, 2),
      in = Set(a, b),
      variables = Set(x, y),
      edges = Set(
        (1, b, Map(x -> List(Cop2(a)), y -> List(Cop2(a), Cop1(x), Cop2(b), Cop1(y), Cop2(a))), 2),
        (1, a, Map(x -> List(Cop1(x)), y -> List(Cop2(a))), 2)
      ),
      q0 = 1,
      partialF = Map(1 -> Set(), 2 -> Set(List()))
    )
    val f = n.presburgerFormula
    val cfg = new java.util.HashMap[String, String]()
    cfg.put("model", "true")
    val ctx = new z3.Context(cfg)
    val freeVars = Seq(a, b).map(a => s"y$a").map(y => y -> ctx.mkIntConst(y))
    val zero = ctx.mkInt(0)
    val positives = freeVars.map { case (_, v) => ctx.mkGe(v, zero) }
    val expr = Presburger.Formula.formulaToZ3Expr(ctx, freeVars.toMap, f)
    val solver = ctx.mkSolver()
    solver.add(expr +: positives: _*)
    assert(solver.check() == z3.Status.SATISFIABLE)
    ctx.close()
  }
}
