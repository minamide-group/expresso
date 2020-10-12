package com.github.kmn4.sst

import com.microsoft.z3._
import org.scalatest.flatspec._

class TestZ3 extends AnyFlatSpec {
  "Presburger formula" should "be checked" in {
    val cfg = new java.util.HashMap[String, String]();
    cfg.put("model", "true")
    val ctx = new Context(cfg)
    val x = ctx.mkIntConst("x")
    val y = ctx.mkIntConst("y")
    val xPlusY = ctx.mkAdd(x, y)
    val three = ctx.mkInt(3)
    val xPlusYEqThree = ctx.mkEq(xPlusY, three)
    val s = ctx.mkSolver()
    s.add(xPlusYEqThree)
    // x + y = 3
    assert(s.check() == Status.SATISFIABLE)
    var m = s.getModel()
    assert(m.eval(x, false).toString.toInt + m.eval(y, false).toString.toInt == 3)

    val xNeg = ctx.mkLt(x, ctx.mkInt(0))
    val yNeg = ctx.mkLt(y, ctx.mkInt(0))
    s.add(xNeg, yNeg)
    // x + y = 3 && x < 0 && y < 0
    assert(s.check() == Status.UNSATISFIABLE)

    s.reset()
    s.add(xPlusYEqThree, xNeg)
    // x + y = 3 && x < 0
    assert(s.check() == Status.SATISFIABLE)
    m = s.getModel()
    assert(m.eval(x, false).toString.toInt + m.eval(y, false).toString.toInt == 3)
    assert(m.eval(x, false).toString.toInt < 0)
    ctx.close()
  }

  "Existantial Presburger formula" should "be checked" in {
    // (exist ((x Int)) (= y (* x 2))) && y > 0
    val cfg = new java.util.HashMap[String, String]();
    cfg.put("model", "true")
    val ctx = new Context(cfg)
    val x = ctx.mkIntConst("x")
    val y = ctx.mkIntConst("y")
    val even = ctx.mkEq(y, ctx.mkMul(x, ctx.mkInt(2)))
    val exists = ctx.mkExists(Array(x), even, 0, null, null, null, null)
    val yPos = ctx.mkGt(y, ctx.mkInt(0))
    val s = ctx.mkSolver()
    s.add(exists, yPos)
    assert(s.check() == Status.SATISFIABLE)
    val m = s.getModel()
    assert(m.eval(y, false).toString.toInt > 0)
    ctx.close()
  }
}
