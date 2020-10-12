package com.github.kmn4.sst.smtlib

import org.scalatest.flatspec._

class TestParser extends AnyFlatSpec {
  "Parser" should "parse" in {
    assert(
      Parser.parse("(declare-const x0 String)")
        == Seq(Call(Symbol("declare-const"), Symbol("x0"), Symbol("String")))
    )
    assert(
      Parser.parse("""(assert (= x1 (str.replaceall x0 "<sc>" "a")))""") ==
        Seq(
          Call(
            Symbol("assert"),
            Call(
              Symbol("="),
              Symbol("x1"),
              Call(Symbol("str.replaceall"), Symbol("x0"), StringConst("<sc>"), StringConst("a"))
            )
          )
        )
    )
    assert(
      Parser.parse("""(assert (= x1 (str.replaceall x0 "<sc>" "a"))) ; Hello! I'm a comment :)
""") ==
        Seq(
          Call(
            Symbol("assert"),
            Call(
              Symbol("="),
              Symbol("x1"),
              Call(Symbol("str.replaceall"), Symbol("x0"), StringConst("<sc>"), StringConst("a"))
            )
          )
        )
    )

    assert(Parser.parse(Example1.input) == Example1.sexpr)
    assert(Parser.parse(Example2.input) == Example2.sexpr)

  }
}
