package com.github.kmn4.sst

import com.microsoft.z3

sealed trait RegExp[+A]
case object EmptyExp extends RegExp[Nothing]
case object EpsExp extends RegExp[Nothing]
case object DotExp extends RegExp[Nothing]
case class CharExp[A, B <: A](b: B) extends RegExp[A]
case class OrExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class CatExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class StarExp[A, B <: A](b: RegExp[B]) extends RegExp[A]
case class CompExp[A, B <: A](b: RegExp[B]) extends RegExp[A]

object Parikh {

  /** Types and constructers for Presburger formula */
  sealed trait Term[X]
  case class Const[X](i: Int) extends Term[X]
  case class Var[X](x: X) extends Term[X]
  case class Add[X](ts: Seq[Term[X]]) extends Term[X]
  case class Sub[X](t1: Term[X], t2: Term[X]) extends Term[X]
  case class Mult[X](c: Const[X], t: Term[X]) extends Term[X]
  sealed trait Formula[X] {
    def smtlib: String = Formula.formulaToSMTLIB(this)
  }
  case class Top[X]() extends Formula[X]
  case class Bot[X]() extends Formula[X]
  case class Eq[X](t1: Term[X], t2: Term[X]) extends Formula[X]
  case class Lt[X](t1: Term[X], t2: Term[X]) extends Formula[X]
  case class Le[X](t1: Term[X], t2: Term[X]) extends Formula[X]
  case class Gt[X](t1: Term[X], t2: Term[X]) extends Formula[X]
  case class Ge[X](t1: Term[X], t2: Term[X]) extends Formula[X]
  case class Conj[X](fs: Seq[Formula[X]]) extends Formula[X]
  case class Disj[X](fs: Seq[Formula[X]]) extends Formula[X]
  case class Not[X](f: Formula[X]) extends Formula[X]
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
    def renameVars[X, Y](f: Formula[X], renamer: X => Y): Formula[Y] = {
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
        case Gt(t1, t2)    => Gt(tm(t1), tm(t2))
        case Ge(t1, t2)    => Ge(tm(t1), tm(t2))
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
      case Gt(t1, t2) => s"(> ${Term.termToSMTLIB(t1)} ${Term.termToSMTLIB(t2)})"
      case Ge(t1, t2) => s"(>= ${Term.termToSMTLIB(t1)} ${Term.termToSMTLIB(t2)})"
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
        case Gt(t1, t2) => ctx.mkGt(fromTerm(t1), fromTerm(t2))
        case Ge(t1, t2) => ctx.mkGe(fromTerm(t1), fromTerm(t2))
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

  type Image[A] = Map[A, Int]
  sealed trait EnftVar[Q, B, E]
  case class BNum[Q, B, E](b: B) extends EnftVar[Q, B, E]
  case class ENum[Q, B, E](e: E) extends EnftVar[Q, B, E]
  case class Dist[Q, B, E](q: Q) extends EnftVar[Q, B, E]
  // case class IsInit[Q, B, E](q: Q) extends EnftVar[Q, B,E]
  // case class IsFin[Q, B, E](q: Q) extends EnftVar[Q, B,E]
  def parikhEnftToPresburgerFormula[Q, A, B](
      enft: ENFT[Q, A, Image[B]]
  ): Formula[EnftVar[Q, B, (Q, Image[B], Q)]] = {
    type Edge = (Q, Image[B], Q)
    type X = EnftVar[Q, B, Edge]
    val states = enft.states.toSeq
    val edges: Seq[Edge] =  {
      for (((q, a), s) <- enft.edges; (r, v) <- s)
        yield (q, v, r)
    } // Need to exclude duplicate.
      .toSet
      .toList
    val edgesFrom: Map[Q, Seq[Edge]] = edges.groupBy(_._1).withDefaultValue(Seq.empty)
    val edgesTo: Map[Q, Seq[Edge]] = edges.groupBy(_._3).withDefaultValue(Seq.empty)
    val input: Map[Q, Term[X]] = states
      .map(q =>
        q ->
          Add[X](
            edgesTo(q)
              .map[Term[X]](e => Var(ENum(e)))
              .appended(
                if (q == enft.initial) Const(1) else Const(0)
              )
          )
      )
      .toMap
    val output: Map[Q, Term[X]] = states
      .map(q =>
        q ->
          Add[X](
            edgesFrom(q)
              .map[Term[X]](e => Var(ENum(e)))
              .appended(
                if (q == enft.finalState) Const(1) else Const(0)
              )
          )
      )
      .toMap
    val euler: Formula[X] = {
      val clauses = states.map(q => Eq(Sub(input(q), output(q)), Const(0)))
      // `caluses` cannot be empty bacause MNFT has at least one state.
      Conj(clauses)
    }
    val connectivity: Formula[X] = {
      val clauses =
        states.map(q => {
          val unreachable = Conj[X](Seq(Eq(Var(Dist(q)), Const(-1)), Eq(output(q), Const(0))))
          val reachable = {
            val isInit: Formula[X] =
              if (q == enft.initial) Eq(Var(Dist(q)), Const(0))
              else Bot()
            val reachedFromSomewhere = edgesTo(q).map(e => {
              val (p, v, _) = e
              Conj(
                List[Formula[X]](
                  Eq(Var(Dist(q)), Add(Seq(Var(Dist(p)), Const(1)))),
                  Gt(Var(ENum(e)), Const(0)),
                  Ge(Var(Dist(p)), Const(0))
                )
              )
            })
            Disj(reachedFromSomewhere.appended(isInit))
          }
          Disj(Seq(unreachable, reachable))
        })
      Conj(clauses)
    }
    val bs = edges.foldLeft[Set[B]](Set.empty) { case (acc, (_, v, _)) => acc union v.keySet }
    val parikh: Formula[X] = {
      val clauses = bs.toSeq.map[Formula[X]](b => {
        val sum: Term[X] = Add(
          edges.map[Term[X]] {
            case (q, v, r) => Mult(Const(v.getOrElse(b, 0)), Var(ENum((q, v, r))))
          }
        )
        Eq(Var(BNum(b)), sum)
      })
      Conj(clauses)
    }
    val boundedVars: Seq[X] = states.map[X](q => Dist(q)) ++ edges.map(e => ENum(e))
    val vars: Seq[X] = boundedVars ++ bs.map(BNum.apply)
    val positive: Formula[X] = Conj(
      vars.map[Formula[X]] {
        case BNum(b) => Ge(Var(BNum(b)), Const(0))
        case ENum(e) => Ge(Var(ENum(e)), Const(0))
        case Dist(q) => Ge(Var(Dist(q)), Const(-1))
      }
    )
    val conj: Formula[X] = Conj(List(euler, connectivity, parikh, positive))
    Exists(boundedVars.map(Var.apply), conj)
  }
  def parikhMnftToPresburgerFormula[Q, A, B](
      mnft: MNFT[Q, A, Image[B]]
  ): Formula[EnftVar[Int, B, (Int, Image[B], Int)]] = {
    parikhEnftToPresburgerFormula(mnft.unifyInitAndFinal)
  }
}
