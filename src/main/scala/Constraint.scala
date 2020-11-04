package com.github.kmn4.sst

// Input .smt2 file must declare string variables in straight-line order,
// and must not declare unused string variables.
object Constraint {
  sealed trait Transduction[A]
  case class ReplaceAll[A](target: Seq[A], word: Seq[A]) extends Transduction[A]
  case class Insert[A](pos: Int, word: Seq[A]) extends Transduction[A]
  case class At[A](pos: Int) extends Transduction[A]
  case class Reverse[A]() extends Transduction[A]
  case class Substr[A](from: Int, len: Int) extends Transduction[A]
  case class TakePrefix[A]() extends Transduction[A]
  case class TakeSuffix[A]() extends Transduction[A]
  case class UntilFirst[A](target: Seq[A]) extends Transduction[A]

  case class StringVar(name: String)
  case class IntVar(name: String)

  sealed trait AtomicConstraint[A]
  case class Constant[A](lhs: StringVar, word: Seq[A]) extends AtomicConstraint[A]
  case class CatCstr[A](lhs: StringVar, rhs: Seq[Either[Seq[A], StringVar]]) extends AtomicConstraint[A]
  case class TransCstr[A](lhs: StringVar, trans: Transduction[A], rhs: StringVar) extends AtomicConstraint[A]

  sealed trait IntExp
  case class ConstExp(i: Int) extends IntExp
  case class VarExp(v: IntVar) extends IntExp
  case class LenExp(v: StringVar) extends IntExp
  case class AddExp(es: Iterable[IntExp]) extends IntExp
  case class SubExp(e1: IntExp, e2: IntExp) extends IntExp
  case class MinusExp(i: IntExp) extends IntExp

  sealed trait IntConstraint
  case class IntEq(e1: IntExp, e2: IntExp) extends IntConstraint
  case class IntLt(e1: IntExp, e2: IntExp) extends IntConstraint
  case class IntConj(cs: Iterable[IntConstraint]) extends IntConstraint
  case class IntDisj(cs: Iterable[IntConstraint]) extends IntConstraint
  case class IntNeg(c: IntConstraint) extends IntConstraint

  case class RegexConstraint[A](v: StringVar, re: RegExp[A])
  case class SLConstraint[A](
      as: Seq[AtomicConstraint[A]],
      is: Seq[IntConstraint],
      rs: Seq[RegexConstraint[A]]
  )

}

object ConstraintExamples {
  import Constraint._
  def replaceAll(s: String, t: String): Transduction[Char] = ReplaceAll(s.toSeq, t.toSeq)
  // Zhu's case 1
  val c1 = {
    val Seq(x0, x1, x2) = (0 to 2).map(i => StringVar(s"x$i"))
    val s1 = TransCstr(x1, replaceAll("a", "b"), x0)
    val s2 = CatCstr(x2, List(Left("a".toList), Right(x1), Left("b".toList)))
    val r = RegexConstraint(x2, CatExp(CatExp(CharExp('a'), StarExp(CharExp('b'))), CharExp('a')))
    SLConstraint(Seq(s1, s2), Nil, Seq(r))
  }
  // Zhu's case 2
  val c2 = {
    val Seq(x0, x1, x2, x3, x4) = (0 to 4).map(i => StringVar(s"x$i"))
    val s1 = TransCstr(x2, replaceAll("<sc>", "a"), x0)
    val s2 = TransCstr(x3, replaceAll("<sc>", "a"), x1)
    val s3 = CatCstr[Char](x4, List(Right(x2), Right(x3)))
    val r = RegexConstraint(x4, "a<sc>a".toSeq.map(CharExp.apply).reduce[RegExp[Char]] {
      case (e1, e2) => CatExp(e1, e2)
    })
    SLConstraint(Seq(s1, s2, s3), Nil, Seq(r))
  }
  // Involving integer constraint
  val c3 = {
    val Seq(x0, x1, x2) = (0 to 2).map(i => StringVar(s"x$i"))
    val s1 = TransCstr(x1, replaceAll("ab", "c"), x0)
    val s2 = TransCstr(x2, replaceAll("ac", "aaaa"), x1)
    val i1 = IntLt(LenExp(x0), ConstExp(5)) // x0 <= 4
    val i2 = IntLt(AddExp(Seq(LenExp(x0), ConstExp(1))), LenExp(x2)) // x0 + 2 <= x2
    SLConstraint(Seq(s1, s2), Seq(i1, i2), Nil)
  }
}
