package com.github.kmn4.sst

sealed trait RegExp[+A] {
  def size = RegExp.size(this)
  def optimizedOne = RegExp.optimizeOne(this)
  def optimized = RegExp.optimize(this)
}
case object EmptyExp extends RegExp[Nothing]
case object EpsExp extends RegExp[Nothing]
case class CharExp[A, B <: A](b: B) extends RegExp[A]
case class OrExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class CatExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class StarExp[A, B <: A](b: RegExp[B]) extends RegExp[A]

object RegExp {
  def size[A](re: RegExp[A]): Int = re match {
    case EpsExp => 1
    case EmptyExp => 1
    case CharExp(_) => 1
    case OrExp(e1, e2) => 1 + size(e1) + size(e2)
    case CatExp(e1, e2) => 1 + size(e1) + size(e2)
    case StarExp(e) => 1 + size(e)
  }
  def optimizeOne[A](re: RegExp[A]): RegExp[A] = re match {
    case OrExp(EmptyExp, e) => e
    case OrExp(e, EmptyExp) => e
    case CatExp(EmptyExp, e) => EmptyExp
    case CatExp(e, EmptyExp) => EmptyExp
    case CatExp(EpsExp, e) => e
    case CatExp(e, EpsExp) => e
    case StarExp(EmptyExp) | StarExp(EpsExp) => EpsExp
    case re => re
  }
  def optimize[A](re: RegExp[A]): RegExp[A] = re match {
    case OrExp(e1, e2) => OrExp(e1.optimized, e2.optimized).optimizedOne
    case CatExp(e1, e2) => OrExp(e1.optimized, e2.optimized).optimizedOne
    case StarExp(e) => StarExp(e.optimized).optimizedOne
    case re => re
  }
}

case class Linear[M](origin: M, vs: Set[M])

object Linear {
  def add[M](l1: Linear[M], l2: Linear[M])(implicit m: Monoid[M]): Linear[M] =
    Linear(m.combine(l1.origin, l2.origin), l1.vs ++ l2.vs)
  def star[M](l: Linear[M])(implicit m: Monoid[M]): Semilinear[M] =
    Semilinear(List(Linear(m.unit, Set.empty), Linear(l.origin, l.vs + l.origin)))

  def toLaTeX(l: Linear[Map[Char, Int]]): String = {
    def fromVec(v: Map[Char, Int]): String = {
      s"""\\left(\\begin{array}{lr}${v.map{ case (c, i) => s"$c:&$i" }.mkString("\\\\")}\\end{array}\\right)"""
    }
    val ss = l.vs.map(fromVec).zipWithIndex.map{ case (s, i) => s"c_{${i+1}}$s" }
    s"""\\left\\{${(ss + fromVec(l.origin)).mkString("+")}\\right\\}"""
  }
}

case class Semilinear[M](ls: List[Linear[M]])

object Semilinear {
  def fromRegex[M](re: RegExp[M])(implicit monoid: Monoid[M]): Semilinear[M] = re match {
    case EmptyExp => Semilinear(List.empty)
    case EpsExp => fromRegex(CharExp(monoid.unit))
    case CharExp(m) => Semilinear(List(Linear(m, Set.empty)))
    case OrExp(e1, e2) => {
      val s1 = fromRegex(e1)
      val s2 = fromRegex(e2)
      Semilinear(s1.ls ++ s2.ls)
    }
    case CatExp(e1, e2) => {
      val s1 = fromRegex(e1)
      val s2 = fromRegex(e2)
      List.from(for (l1 <- s1.ls; l2 <- s2.ls) yield Linear.add(l1, l2))
        .foldRight(Semilinear(List.empty[Linear[M]])){ case (l, acc) => Semilinear(l :: acc.ls) }
    }
    case StarExp(e) => {
      val s = fromRegex(e)
      s.ls
        .map(Linear.star(_))
        .foldRight(Semilinear(List(Linear(monoid.unit, Set.empty)))) { case (s, acc) => Semilinear(s.ls ++ acc.ls) }
    }
  }

  def toLaTeX(s: Semilinear[Map[Char, Int]]): String =
    s"&${s.ls.map(Linear.toLaTeX).mkString("\\\\\\cup&")}"

}
