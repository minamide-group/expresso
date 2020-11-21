package com.github.kmn4.sst

import com.microsoft.z3

object Presburger {

  /** Types and constructers for Presburger formula */
  sealed trait Term[X] {
    def eval(valuation: Map[X, Int]): Int = this match {
      case Const(i)          => i
      case Var(x)            => valuation(x)
      case Add(ts)           => ts.map(_.eval(valuation)).sum
      case Sub(t1, t2)       => t1.eval(valuation) - t2.eval(valuation)
      case Mult(Const(i), t) => i * t.eval(valuation)
    }
  }
  case class Const[X](i: Int) extends Term[X]
  case class Var[X](x: X) extends Term[X]
  case class Add[X](ts: Seq[Term[X]]) extends Term[X]
  case class Sub[X](t1: Term[X], t2: Term[X]) extends Term[X]
  case class Mult[X](c: Const[X], t: Term[X]) extends Term[X]
  sealed trait Formula[X] {
    def smtlib: String = Formula.formulaToSMTLIB(this)

    def renameVars[Y](renamer: X => Y): Formula[Y] = Formula.renameVars(this)(renamer)

    /** @throws UnsupportedOperationException if this contains Exists. */
    def eval(valuation: Map[X, Int]): Boolean = this match {
      case Top()        => true
      case Bot()        => false
      case Eq(t1, t2)   => t1.eval(valuation) == t2.eval(valuation)
      case Lt(t1, t2)   => t1.eval(valuation) < t2.eval(valuation)
      case Le(t1, t2)   => t1.eval(valuation) <= t2.eval(valuation)
      case Conj(fs)     => fs.find(!_.eval(valuation)).isEmpty
      case Disj(fs)     => fs.find(_.eval(valuation)).nonEmpty
      case Not(f)       => !f.eval(valuation)
      case Exists(_, _) => throw new UnsupportedOperationException("Cannot evaluate formula with quantifier.")
    }
  }
  case class Top[X]() extends Formula[X]
  case class Bot[X]() extends Formula[X]
  case class Eq[X](t1: Term[X], t2: Term[X]) extends Formula[X]
  case class Lt[X](t1: Term[X], t2: Term[X]) extends Formula[X]
  case class Le[X](t1: Term[X], t2: Term[X]) extends Formula[X]
  def Gt[X](t1: Term[X], t2: Term[X]): Formula[X] = Lt(t2, t1)
  def Ge[X](t1: Term[X], t2: Term[X]): Formula[X] = Le(t2, t1)
  case class Conj[X](fs: Seq[Formula[X]]) extends Formula[X]
  case class Disj[X](fs: Seq[Formula[X]]) extends Formula[X]
  case class Not[X](f: Formula[X]) extends Formula[X]
  def Implies[X](pre: Formula[X], post: Formula[X]): Formula[X] = Disj(Seq(Not(pre), post))
  def Equiv[X](f1: Formula[X], f2: Formula[X]): Formula[X] = Conj(Seq(Implies(f1, f2), Implies(f2, f1)))
  case class Exists[X](vs: Seq[Var[X]], f: Formula[X]) extends Formula[X]

  object Term {
    def termToSMTLIB[X](t: Term[X]): String = t match {
      case Const(i)     => i.toString()
      case Var(x)       => x.toString()
      case Add(ts)      => s"""(+ 0 ${ts.map(termToSMTLIB).mkString(" ")})"""
      case Sub(t1, t2)  => s"(- ${termToSMTLIB(t1)} ${termToSMTLIB(t2)})"
      case Mult(t1, t2) => s"(* ${termToSMTLIB(t1)} ${termToSMTLIB(t2)})"
    }
  }

  object Formula {
    def renameVars[X, Y](f: Formula[X])(renamer: X => Y): Formula[Y] = {
      def tm(t: Term[X]): Term[Y] = {
        def aux(t: Term[X]): Term[Y] = t match {
          case Const(i)          => Const(i)
          case Var(x)            => Var(renamer(x))
          case Add(ts)           => Add(ts.map(aux))
          case Sub(t1, t2)       => Sub(aux(t1), aux(t2))
          case Mult(Const(i), t) => Mult(Const(i), aux(t))
        }
        aux(t)
      }
      def aux(f: Formula[X]): Formula[Y] = f match {
        case Top()         => Top()
        case Bot()         => Bot()
        case Eq(t1, t2)    => Eq(tm(t1), tm(t2))
        case Lt(t1, t2)    => Lt(tm(t1), tm(t2))
        case Le(t1, t2)    => Le(tm(t1), tm(t2))
        case Conj(fs)      => Conj(fs.map(aux))
        case Disj(fs)      => Disj(fs.map(aux))
        case Not(f)        => Not(aux(f))
        case Exists(xs, f) => Exists(xs.map { case Var(x) => Var(renamer(x)) }, aux(f))
      }
      aux(f)
    }
    def formulaToSMTLIB[X](f: Formula[X]): String = f match {
      case Top()      => "(= 0 0)"
      case Bot()      => "(= 0 1)"
      case Eq(t1, t2) => s"(= ${Term.termToSMTLIB(t1)} ${Term.termToSMTLIB(t2)})"
      case Lt(t1, t2) => s"(< ${Term.termToSMTLIB(t1)} ${Term.termToSMTLIB(t2)})"
      case Le(t1, t2) => s"(<= ${Term.termToSMTLIB(t1)} ${Term.termToSMTLIB(t2)})"
      case Conj(fs) => {
        val fsString = fs.map(formulaToSMTLIB).mkString(" ")
        s"(and true $fsString)"
      }
      case Disj(fs) => {
        val fsString = fs.map(formulaToSMTLIB).mkString(" ")
        s"(or false $fsString)"
      }
      case Not(f) => s"(not ${formulaToSMTLIB(f)})"
      case Exists(xs, f) => {
        val xsString = xs.map { case Var(x) => s"(${x.toString()} Int)" }.mkString(" ")
        s"(exists (${xsString}) ${formulaToSMTLIB(f)})"
      }
    }

    /** Convert a given formula to z3.BoolExpr. */
    def formulaToExpr[X](
        ctx: z3.Context,
        freeVars: Map[X, z3.IntExpr],
        f: Formula[X]
    ): z3.BoolExpr = {
      var varMap = freeVars
      val trueExpr = ctx.mkBool(true)
      val falseExpr = ctx.mkBool(false)
      def newVar(x: X): z3.IntExpr = {
        val e = ctx.mkIntConst(x.toString())
        varMap += (x -> e)
        e
      }
      def fromTerm(t: Term[X]): z3.ArithExpr = t match {
        case Const(i)    => ctx.mkInt(i)
        case Var(x)      => varMap.getOrElse(x, newVar(x))
        case Add(ts)     => ctx.mkAdd(ts.map(fromTerm): _*)
        case Sub(t1, t2) => ctx.mkSub(fromTerm(t1), fromTerm(t2))
        case Mult(c, t)  => ctx.mkMul(fromTerm(c), fromTerm(t))
      }
      def fromFormula(f: Formula[X]): z3.BoolExpr = f match {
        case Top()      => trueExpr
        case Bot()      => falseExpr
        case Eq(t1, t2) => ctx.mkEq(fromTerm(t1), fromTerm(t2))
        case Lt(t1, t2) => ctx.mkLt(fromTerm(t1), fromTerm(t2))
        case Le(t1, t2) => ctx.mkLe(fromTerm(t1), fromTerm(t2))
        case Conj(fs)   => ctx.mkAnd(fs.map(fromFormula): _*)
        case Disj(fs)   => ctx.mkOr(fs.map(fromFormula): _*)
        case Not(f)     => ctx.mkNot(fromFormula(f))
        case Exists(vs, f) => {
          val xs = vs.map { case Var(x) => newVar(x) }
          val body = formulaToExpr(ctx, varMap, f)
          ctx.mkExists(xs.toArray, body, 0, null, null, null, null)
        }
      }
      fromFormula(f)
    }
  }

}