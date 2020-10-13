package com.github.kmn4.sst.smtlib

/** S-expression.
  * constant ::= numeral | string
  * sexp ::= constant | symbol | '(' sexp... ')'*/
sealed trait SExpr
sealed trait Const extends SExpr
case class NumConst(i: Int) extends Const
case class StringConst(s: String) extends Const
case class Symbol(name: String) extends SExpr
case class Call(ss: SExpr*) extends SExpr

sealed trait Sort
case object IntSort extends Sort
case object StringSort extends Sort

/** Special forms. */
sealed trait Form
case class DeclConst(name: String, sort: Sort) extends Form
case class Assert(e: SExpr) extends Form
case object CheckSAT extends Form
case object GetModel extends Form

object Form {
  def fromSExpr(s: SExpr): Form = s match {
    case Call(Symbol("declare-const"), Symbol(name), Symbol("Int")) =>
      DeclConst(name, IntSort)
    case Call(Symbol("declare-fun"), Symbol(name), Call(), Symbol("Int")) =>
      DeclConst(name, IntSort)
    case Call(Symbol("declare-const"), Symbol(name), Symbol("String")) =>
      DeclConst(name, StringSort)
    case Call(Symbol("declare-fun"), Symbol(name), Call(), Symbol("String")) =>
      DeclConst(name, StringSort)
    case Call(Symbol("assert"), expr) => Assert(expr)
    case Call(Symbol("check-sat"))    => CheckSAT
    case Call(Symbol("get-model"))    => GetModel
    case _                            => throw new Exception("Cannot interpret given S expression as a form.")
  }
}
