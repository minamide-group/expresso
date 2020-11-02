package com.github.kmn4.sst.smtlib2

object Example1 {
  val input = """
(declare-const x0 String)
(declare-const x1 String)
(declare-const y0 String)
(declare-const y1 String)
(declare-const xy String)

(assert (= x1 (str.replaceall x0 "<sc>" "a"))) ; Hello! I'm a comment :)
(assert (= y1 (str.replaceall y0 "<sc>" "a")))
(assert (= xy (str.++ x1 y1)))
(assert (str.in.re xy (str.to.re "a<sc>a")))
"""
  val sexpr = List(
    Call(Symbol("declare-const"), Symbol("x0"), Symbol("String")),
    Call(Symbol("declare-const"), Symbol("x1"), Symbol("String")),
    Call(Symbol("declare-const"), Symbol("y0"), Symbol("String")),
    Call(Symbol("declare-const"), Symbol("y1"), Symbol("String")),
    Call(Symbol("declare-const"), Symbol("xy"), Symbol("String")),
    Call(
      Symbol("assert"),
      Call(
        Symbol("="),
        Symbol("x1"),
        Call(Symbol("str.replaceall"), Symbol("x0"), StringConst("<sc>"), StringConst("a"))
      )
    ),
    Call(
      Symbol("assert"),
      Call(
        Symbol("="),
        Symbol("y1"),
        Call(Symbol("str.replaceall"), Symbol("y0"), StringConst("<sc>"), StringConst("a"))
      )
    ),
    Call(
      Symbol("assert"),
      Call(Symbol("="), Symbol("xy"), Call(Symbol("str.++"), Symbol("x1"), Symbol("y1")))
    ),
    Call(
      Symbol("assert"),
      Call(Symbol("str.in.re"), Symbol("xy"), Call(Symbol("str.to.re"), StringConst("a<sc>a")))
    )
  )

  val form = List(
    DeclConst("x0", StringSort),
    DeclConst("x1", StringSort),
    DeclConst("y0", StringSort),
    DeclConst("y1", StringSort),
    DeclConst("xy", StringSort),
    Assert(
      Call(
        Symbol("="),
        Symbol("x1"),
        Call(Symbol("str.replaceall"), Symbol("x0"), StringConst("<sc>"), StringConst("a"))
      )
    ),
    Assert(
      Call(
        Symbol("="),
        Symbol("y1"),
        Call(Symbol("str.replaceall"), Symbol("y0"), StringConst("<sc>"), StringConst("a"))
      )
    ),
    Assert(
      Call(Symbol("="), Symbol("xy"), Call(Symbol("str.++"), Symbol("x1"), Symbol("y1")))
    ),
    Assert(
      Call(Symbol("str.in.re"), Symbol("xy"), Call(Symbol("str.to.re"), StringConst("a<sc>a")))
    ),
    Call(Symbol("check-sat")),
    Call(Symbol("get-model"))
  )
}

object Example2 {
  val input = """
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= y (str.replaceall x "ab" "c")))
(assert (= z (str.replaceall y "ac" "aaaa")))
(assert (< (str.len x) 5))
(assert (< (+ (str.len x) 1) (str.len z)))
(check-sat)
(get-model)
"""
  val sexpr = List(
    Call(Symbol("declare-const"), Symbol("x"), Symbol("String")),
    Call(Symbol("declare-const"), Symbol("y"), Symbol("String")),
    Call(Symbol("declare-const"), Symbol("z"), Symbol("String")),
    Call(
      Symbol("assert"),
      Call(
        Symbol("="),
        Symbol("y"),
        Call(Symbol("str.replaceall"), Symbol("x"), StringConst("ab"), StringConst("c"))
      )
    ),
    Call(
      Symbol("assert"),
      Call(
        Symbol("="),
        Symbol("z"),
        Call(Symbol("str.replaceall"), Symbol("y"), StringConst("ac"), StringConst("aaaa"))
      )
    ),
    Call(Symbol("assert"), Call(Symbol("<"), Call(Symbol("str.len"), Symbol("x")), NumConst(5))),
    Call(
      Symbol("assert"),
      Call(
        Symbol("<"),
        Call(Symbol("+"), Call(Symbol("str.len"), Symbol("x")), NumConst(1)),
        Call(Symbol("str.len"), Symbol("z"))
      )
    ),
    Call(Symbol("check-sat")),
    Call(Symbol("get-model"))
  )
}
