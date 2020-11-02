package com.github.kmn4.sst

// Input .smt2 file must declare string variables in straight-line order,
// and must not declare unused string variables.
object Constraint {
  sealed trait Transduction[A]
  case class PrependAppend[A](pre: Seq[A], post: Seq[A]) extends Transduction[A]
  case class ReplaceAll[A](target: Seq[A], word: Seq[A]) extends Transduction[A]
  case class Insert[A](pos: Int, word: Seq[A]) extends Transduction[A]
  case class At[A](pos: Int) extends Transduction[A]
  case class Reverse[A]() extends Transduction[A]
  case class Substr[A](from: Int, len: Int) extends Transduction[A]
  case class TakePrefix[A]() extends Transduction[A]
  case class TakeSuffix[A]() extends Transduction[A]

  case class StringVar(name: String)
  case class IntVar(name: String)

  sealed trait AtomicConstraint[A]
  case class Constant[A](lhs: StringVar, word: Seq[A]) extends AtomicConstraint[A]
  case class CatCstr[A](lhs: StringVar, rhs1: StringVar, rhs2: StringVar) extends AtomicConstraint[A]
  case class TransCstr[A](lhs: StringVar, trans: Transduction[A], rhs: StringVar) extends AtomicConstraint[A]

  sealed trait IntExp
  case class ConstExp(i: Int) extends IntExp
  case class VarExp(v: IntVar) extends IntExp
  case class LenExp(v: StringVar) extends IntExp
  case class AddExp(es: Iterable[IntExp]) extends IntExp
  case class SubExp(e1: IntExp, e2: IntExp) extends IntExp

  sealed trait IntConstraint
  case class IntEq(e1: IntExp, e2: IntExp) extends IntConstraint
  case class IntLt(e1: IntExp, e2: IntExp) extends IntConstraint
  case class IntConj(cs: Iterable[IntConstraint]) extends IntConstraint
  case class IntNeg(c: IntConstraint) extends IntConstraint

  case class RegexConstraint[A](v: StringVar, re: RegExp[A])
  case class SLConstraint[A](
      as: Seq[AtomicConstraint[A]],
      is: Seq[IntConstraint],
      rs: Seq[RegexConstraint[A]]
  )

  object SLConstraint {
    import smtlib2._
    private type Env = Map[String, Sort]
    private sealed trait BoolExp
    private case class Atom(a: AtomicConstraint[Char]) extends BoolExp
    private case class IntC(i: IntConstraint) extends BoolExp
    private case class REC(r: RegexConstraint[Char]) extends BoolExp
    private def expectTransduction(e: SExpr, env: Env): (String, Transduction[Char]) = e match {
      case Call(Symbol("str.++"), StringConst(pre), Symbol(name), StringConst(post))
          if env(name) == StringSort =>
        (name, PrependAppend(pre, post))
      case Call(Symbol("str.replaceall"), Symbol(name), StringConst(target), StringConst(word))
          if env(name) == StringSort =>
        (name, ReplaceAll(target, word))
      case Call(Symbol("str.at"), Symbol(name), NumConst(pos)) if env(name) == StringSort => (name, At(pos))
      case Call(Symbol("str.insert"), Symbol(name), NumConst(pos), StringConst(word))
          if env(name) == StringSort =>
        (name, Insert(pos, word))
      case Call(Symbol("str.reverse"), Symbol(name)) if env(name) == StringSort => (name, Reverse())
      case Call(Symbol("str.substr"), Symbol(name), NumConst(from), NumConst(len)) =>
        (name, Substr(from, len))
      case Call(Symbol("str.take_prefix"), Symbol(name)) if env(name) == StringSort => (name, TakePrefix())
      case Call(Symbol("str.take_suffix"), Symbol(name)) if env(name) == StringSort => (name, TakeSuffix())
      case _                                                                        => throw new Exception("Cannot interpret given S-expression as transduction")
    }
    private def expectInt(e: SExpr, env: Env): IntExp = e match {
      case NumConst(i)                                                      => ConstExp(i)
      case Symbol(name) if env(name) == IntSort                             => VarExp(IntVar(name))
      case Call(Symbol("str.len"), Symbol(name)) if env(name) == StringSort => LenExp(StringVar(name))
      case Call(Symbol("+"), es @ _*)                                       => AddExp(es.map(expectInt(_, env)))
      case Call(Symbol("-"), e1, e2)                                        => SubExp(expectInt(e1, env), expectInt(e2, env))
      case _                                                                => throw new Exception("Cannot interpret given S-expression as int expression")
    }
    private def expectRegExp(e: SExpr): RegExp[Char] =
      e match {
        case Call(Symbol("str.to.re"), StringConst(s)) =>
          if (s.nonEmpty)
            s.map[RegExp[Char]](CharExp.apply).reduce[RegExp[Char]] { case (e1, e2) => CatExp(e1, e2) }
          else EpsExp
        case Call(Symbol("re.*"), e) => StarExp(expectRegExp(e))
        case Call(Symbol("re.+"), e) =>
          val re = expectRegExp(e)
          CatExp(re, StarExp(re))
        case Call(Symbol("re.++"), e1, e2)    => CatExp(expectRegExp(e1), expectRegExp(e2))
        case Call(Symbol("re.union"), e1, e2) => OrExp(expectRegExp(e1), expectRegExp(e2))
        case Call(Symbol("re.range"), StringConst(c1), StringConst(c2)) if c1.length == 1 && c2.length == 1 =>
          throw new NotImplementedError("re.range is not implemented")
        case Call(Symbol("re.comp"), e) => CompExp(expectRegExp(e))
        case Symbol("re.allchar")       => DotExp
        case Symbol("re.all")           => StarExp(DotExp)
        case _                          => throw new Exception(s"Cannot interpret given S-expression as regular expression: $e")
      }
    private def expectConstraint(e: SExpr, env: Env): BoolExp = e match {
      case Call(Symbol("="), Symbol(name), StringConst(s)) if env(name) == StringSort =>
        Atom(Constant(StringVar(name), s))
      case Call(Symbol("="), Symbol(name), Call(Symbol("str.++"), Symbol(rhs1), Symbol(rhs2)))
          if env(name) == StringSort && env(rhs1) == StringSort && env(rhs2) == StringSort =>
        Atom(CatCstr(StringVar(name), StringVar(rhs1), StringVar(rhs2)))
      case Call(Symbol("="), Symbol(name), e) if env(name) == StringSort =>
        val (rhs, trans) = expectTransduction(e, env)
        Atom(TransCstr(StringVar(name), trans, StringVar(rhs)))
      case Call(Symbol("="), e1, e2) =>
        val i1 = expectInt(e1, env)
        val i2 = expectInt(e2, env)
        IntC(IntEq(i1, i2))
      case Call(Symbol("<"), e1, e2) =>
        val i1 = expectInt(e1, env)
        val i2 = expectInt(e2, env)
        IntC(IntLt(i1, i2))
      case Call(Symbol("<="), e1, e2) =>
        val i1 = expectInt(e1, env)
        val i2 = expectInt(e2, env)
        IntC(IntNeg(IntLt(i2, i1)))
      case Call(Symbol(">"), e1, e2) =>
        val i1 = expectInt(e1, env)
        val i2 = expectInt(e2, env)
        IntC(IntLt(i2, i1))
      case Call(Symbol(">="), e1, e2) =>
        val i1 = expectInt(e1, env)
        val i2 = expectInt(e2, env)
        IntC(IntNeg(IntLt(i1, i2)))
      case Call(Symbol("not"), e) =>
        expectConstraint(e, env) match {
          case IntC(i) => IntC(IntNeg(i))
          case _       => throw new Exception(s"Not supported negation.")
        }
      case Call(Symbol("str.in.re"), Symbol(name), e) if env(name) == StringSort =>
        REC(RegexConstraint(StringVar(name), expectRegExp(e)))
      case _ => throw new Exception(s"Cannot interpret given expression as of Bool sort.")
    }
    def fromFormsAndEnv(forms: List[Form], env: Env): SLConstraint[Char] = forms match {
      case Nil => SLConstraint(Nil, Nil, Nil)
      case DeclConst(name, sort) :: rest =>
        if (env.isDefinedAt(name)) throw new Exception(s"Duplicate declaration of $name")
        else fromFormsAndEnv(rest, env + (name -> sort))
      case Assert(e) :: rest =>
        val cstr = expectConstraint(e, env)
        val SLConstraint(as, is, rs) = fromFormsAndEnv(rest, env)
        cstr match {
          case Atom(a) => SLConstraint(a +: as, is, rs)
          case IntC(i) => SLConstraint(as, i +: is, rs)
          case REC(r)  => SLConstraint(as, is, r +: rs)
        }
      // TODO
      case CheckSAT :: rest => SLConstraint(Nil, Nil, Nil)
      case GetModel :: rest => SLConstraint(Nil, Nil, Nil)
    }
    def fromForms(forms: Seq[Form]): SLConstraint[Char] = fromFormsAndEnv(forms.toList, Map.empty)
  }
}

object ConstraintExamples {
  import Constraint._
  def replaceAll(s: String, t: String): Transduction[Char] = ReplaceAll(s.toSeq, t.toSeq)
  // Zhu's case 1
  val c1 = {
    val Seq(x0, x1, x2) = (0 to 2).map(i => StringVar(s"x$i"))
    val s1 = TransCstr(x1, replaceAll("a", "b"), x0)
    val s2 = TransCstr(x2, PrependAppend("a".toSeq, "b".toSeq), x1)
    val r = RegexConstraint(x2, CatExp(CatExp(CharExp('a'), StarExp(CharExp('b'))), CharExp('a')))
    SLConstraint(Seq(s1, s2), Nil, Seq(r))
  }
  // Zhu's case 2
  val c2 = {
    val Seq(x0, x1, x2, x3, x4) = (0 to 4).map(i => StringVar(s"x$i"))
    val s1 = TransCstr(x2, replaceAll("<sc>", "a"), x0)
    val s2 = TransCstr(x3, replaceAll("<sc>", "a"), x1)
    val s3 = CatCstr[Char](x4, x2, x3)
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
