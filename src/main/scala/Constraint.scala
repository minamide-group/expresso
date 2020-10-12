package com.github.kmn4.sst

// Input .smt2 file must declare string variables in straight-line order,
// and must not declare unused string variables.
object Constraint {
  sealed trait Transduction[A]
  case class PrependAppend[A](pre: Seq[A], post: Seq[A]) extends Transduction[A]
  case class ReplaceAll[A](target: Seq[A], word: Seq[A]) extends Transduction[A]
  case class Insert[A](pos: Int, word: Seq[A]) extends Transduction[A]
  case class At[A](pos: Int) extends Transduction[A]

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
    import smtlib._
    private type Env = Map[String, Sort]
    private sealed trait BoolExp
    private case class Atom(a: AtomicConstraint[Char]) extends BoolExp
    private case class IntC(i: IntConstraint) extends BoolExp
    private case class REC(r: RegexConstraint[Char]) extends BoolExp
    private def expectTransduction(e: SExpr, env: Env): (String, Transduction[Char]) = e match {
      case Call(Symbol("str.replaceall"), Symbol(name), StringConst(target), StringConst(word))
          if env(name) == StringSort =>
        (name, ReplaceAll(target, word))
      // case Call(Symbol("str."))
      case _ => throw new Exception("Cannot interpret given S-expression as transduction")
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
        case _ => throw new Exception("Cannot interpret given S-expression as regular expression")
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
      case CheckSAT :: rest => ???
      case GetModel :: rest => ???
    }
    def fromForms(forms: Seq[Form]): SLConstraint[Char] = fromFormsAndEnv(forms.toList, Map.empty)
  }
}

object ConstraintExamples {
  import Constraint._
  import RegExp._
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

object Solver {
  // Returns update which appends `w` to variable `x`, and is identity on other variables in `xs`.
  def appendWordTo[X, A](x: X, xs: Set[X], w: List[A]): Concepts.Update[X, A] =
    xs.map(y => y -> (List(Cop1(y)) ++ (if (y == x) w.map(Cop2(_)) else Nil))).toMap

  // Returns NSST whose states `q`s are embedded to Cop2(q).
  def embedStates2[P, Q, A, B, X](n: NSST[Q, A, B, X]): NSST[Cop[P, Q], A, B, X] = {
    new NSST(
      n.states.map(Cop2(_)),
      n.in,
      n.variables,
      n.edges.map { case (q, a, m, r) => (Cop2(q), a, m, Cop2(r)) },
      Cop2(n.q0),
      n.partialF.map { case (q, s) => Cop2(q) -> s }
    )
  }

  /** Returns `alphabet` to `alphabet` NSST whose state set is {(0, 0), ... (n, 0)}
    * and variable set is `inputVariable +: otherVariables`.
    * On each state (i, 0) the NSST appends input character to `inputVariable`, and identity on `otherVariables`.
    * It transitions to next state when it reads `None`, appending `None` to `inputVariable`.
    * Its output function value will be `Set(output)` on state (n, 0), and empty on other ones.
    * So the NSST reads string of the form "w0 None w1 None ... w(n-1) None" and
    * outputs `output` where `inputVariable` is replaced with "w0 None ... w(n-1) None". */
  def solverNsstTemplate[C, X](
      n: Int,
      alphabet: Set[C],
      inputVariable: X,
      otherVariables: Set[X],
      output: List[Cop[X, Option[C]]]
  ): NSST[(Int, Int), Option[C], Option[C], X] = {
    type Q = (Int, Int)
    type A = Option[C]
    type B = Option[C]
    val states = Set.from(for (i <- 0 to n) yield (i, 0))
    val xs = otherVariables + inputVariable
    val outF: Map[Q, Set[Concepts.Cupstar[X, B]]] = Map((n, 0) -> Set(output))
    val updates = Concepts.updateMonoid(xs)
    type Edges = Set[(Q, A, Concepts.Update[X, B], Q)]
    val edges: Edges = {
      val appendingEdges: Edges =
        for ((i, _) <- states; a <- alphabet if i != n)
          yield (
            (i, 0),
            Some(a),
            updates.unit + (inputVariable -> List(Cop1(inputVariable), Cop2(Some(a)))),
            (i, 0)
          )
      val toNextEdges: Edges =
        for ((i, _) <- states; if i != n)
          yield (
            (i, 0),
            None,
            updates.unit + (inputVariable -> List(Cop1(inputVariable), Cop2(None))),
            (i + 1, 0)
          )
      appendingEdges ++ toNextEdges
    }
    new NSST(
      states,
      (alphabet.map[Option[C]](Some(_))) + None,
      xs,
      edges,
      (0, 0),
      outF
    )
  }

  /** Construct DFA which accepts strings whose postfix is target.
    *  Each state i represents target.substring(0, i). */
  private def postfixDFA[A](target: Seq[A], in: Set[A]): DFA[Int, A] = {
    // KMP backtracking table
    val table: Vector[Int] = {
      var t = Vector(-1)
      for (i <- 1 until target.length) {
        val prev = t(i - 1)
        t = t.appended(prev + (if (target(i - 1) == target(prev + 1)) 1 else 0))
      }
      t
    }
    val states = Set.from(0 to target.length)
    val q0 = 0
    val qf = target.length
    val delta = Map.from {
      for (q <- states; a <- in if q != qf)
        yield (q, a) -> {
          var j = q
          while (j >= 0 && a != target(j)) {
            j = table(j)
          }
          j + 1
        }
    }
    new DFA(
      states,
      in,
      delta,
      q0,
      Set(qf)
    )
  }

  /** Construct NSST which replaces `target` in `j`-th input string with `word`,
    * and output it as `i`-th string. */
  def replaceAllNSST[C](
      target: Seq[C],
      word: Seq[C],
      i: Int,
      j: Int,
      in: Set[C]
  ): NSST[Int, Option[C], Option[C], Int] = {
    if (i <= j) {
      throw new Exception()
    }
    type Q = (Int, Int)
    sealed trait X
    case object XIn extends X
    case object XJ extends X
    type A = Option[C]
    type B = Option[C]
    type Update = Concepts.Update[X, B]
    val base = solverNsstTemplate[C, X](i, in, XIn, Set(XJ), List(Cop1(XIn), Cop1(XJ), Cop2(None)))
    val xs = base.variables
    val updates: Monoid[Update] = Concepts.updateMonoid(xs)
    val dfa = postfixDFA(target, in)
    type Edges = Set[(Q, A, Update, Q)]
    val edges: Edges = {
      val notFromJ: Edges = {
        val baseEdges = base.edges.filter { case ((q, _), a, _, _) => q != j && !(q == j - 1 && a == None) }
        // On state (j-1, 0), machine should transition to (j, q0) by reading None.
        baseEdges + (
          (
            (j - 1, 0),
            None,
            updates.unit + (XIn -> List(Cop1(XIn), Cop2(None))),
            (j, dfa.q0)
          )
        )
      }
      val jthComponent: Edges = {
        val states = dfa.states -- dfa.finalStates
        // On each state q, DFA has partially matched prefix of target string.
        // If translated SST reads None, it should append the stored string to variable i.
        val toNext: Edges =
          states.map(q => {
            val stored = target.take(q)
            val appendStored: Update = {
              Map(
                XIn -> List(Cop1(XIn), Cop2(None)),
                XJ -> (List(Cop1(XJ)) ++ stored.toList.map(a => Cop2(Some(a))))
              )
            }
            ((j, q), None, appendStored, (j + 1, 0))
          })
        // In each transition, DFA discards some prefix string (possibly empty one).
        // SST should store it in variable 1 (it should also store input char in 0, of course).
        val edgesFromDfa: Edges = {
          for (q <- states; a <- in)
            yield {
              val t = dfa.transition((q, a))
              val (r, append) =
                if (dfa.finalStates contains t) (dfa.q0, word.map(Some(_)))
                else {
                  val qStored = target.take(q) ++ List(a)
                  (t, qStored.take(qStored.length - t).toList.map(Some(_)))
                }
              val m = updates.combine(
                appendWordTo(XIn, xs, List(Some(a))),
                appendWordTo(XJ, xs, append.toList)
              )
              ((j, q), Some(a), m, (j, r))
            }
        }
        edgesFromDfa ++ toNext
      }
      (notFromJ ++ jthComponent)
    }
    val states = edges.map { case (q, _, _, _) => q } + ((i, 0))
    val q0 = if (j == 0) (j, dfa.q0) else (0, 0)
    new NSST[Q, A, B, X](
      states,
      in.map(Some(_): Option[C]) + None,
      xs,
      edges,
      q0,
      base.partialF
    ).renamed
  }

  /** Construct NSST which output concatenation of `j`-th and `k`-th input in this order. */
  def concatNSST[C](i: Int, j: Int, k: Int, alphabet: Set[C]): NSST[Int, Option[C], Option[C], Int] = {
    type Q = (Int, Int)
    type A = Option[C]
    type B = Option[C]
    trait X
    case object XIn extends X
    case object XJ extends X
    case object XK extends X
    val base: NSST[Q, A, B, X] =
      solverNsstTemplate(i, alphabet, XIn, Set(XJ, XK), List(Cop1(XIn), Cop1(XJ), Cop1(XK), Cop2(None)))
    val updates = Concepts.updateMonoid(base.variables)
    val edges = {
      base.edges.map {
        case (q, a, m, r) if j == k && q._1 == j && a != None =>
          (q, a, m + (XJ -> List(Cop1(XJ), Cop2(a))) + (XK -> List(Cop1(XK), Cop2(a))), r)
        case (q, a, m, r) if q._1 == j && a != None => (q, a, m + (XJ -> List(Cop1(XJ), Cop2(a))), r)
        case (q, a, m, r) if q._1 == k && a != None => (q, a, m + (XK -> List(Cop1(XK), Cop2(a))), r)
        case other                                  => other
      }
    }
    new NSST[Q, A, B, X](
      base.states,
      alphabet.map[Option[C]](Some.apply) + None,
      base.variables,
      edges.toSet,
      (0, 0),
      base.outF
    ).renamed
  }

  // Construct NSST which outputs exactly the same string as input,
  // if it is consist of `n` strings and its `i`-th (starting from 0) one
  // is in language represented by `re`.
  def regexNSST(
      n: Int,
      i: Int,
      re: RegExp[Char],
      alphabet: Set[Char]
  ): NSST[Int, Option[Char], Option[Char], Int] = {
    type DQ = Int
    val dfa: DFA[DQ, Char] = new RegExp2NFA(re).construct().toDFA.minimized.renamed
    type Q = Cop[DQ, Int]
    type A = Option[Char]
    type B = Option[Char]
    type X = Unit

    val base: NSST[Q, A, B, X] = {
      val states = Set.from(0 to n) - i
      val xs = Set(())
      val q0 = 0
      val outF: Map[Int, Set[Concepts.Cupstar[X, B]]] = Map(n -> Set(List(Cop1(()))))
      val updates = Concepts.updateMonoid(xs)
      type Edges = Set[(Int, A, Concepts.Update[X, B], Int)]
      val edges: Edges = {
        val appendingEdges: Edges =
          for (j <- states; a <- alphabet if j != n && j != i)
            yield (j, Some(a), updates.unit + (() -> List(Cop1(()), Cop2(Some(a)))), j)
        val toNextEdges: Edges =
          for (j <- states; if j != n && j + 1 != i)
            yield (j, None, updates.unit + (() -> List(Cop1(()), Cop2(None))), j + 1)
        appendingEdges ++ toNextEdges
      }
      embedStates2(
        new NSST(
          states,
          (alphabet.map[Option[Char]](Some(_))) + None,
          xs,
          edges,
          q0,
          outF
        )
      )
    }

    type Update = Concepts.Update[X, B]
    type Edge = (Q, A, Update, Q)
    type Edges = Set[Edge]
    // Replace state i with states of DFA.
    val states = base.states - Cop2(i) ++ dfa.states.map(Cop1.apply)
    val updates = Concepts.updateMonoid(base.variables)
    val edges: Edges = {
      base.edges +
        ((Cop2(i - 1), None, updates.unit + (() -> List(Cop1(()), Cop2(None))), Cop1(dfa.q0))) ++
        dfa.finalStates.map[Edge](q =>
          (Cop1(q), None, updates.unit + (() -> List(Cop1(()), Cop2(None))), Cop2(i + 1))
        ) ++
        dfa.transition.map[Edge] {
          case ((q, a), r) => {
            val m = updates.unit + (() -> List(Cop1(()), Cop2(Some(a))))
            (Cop1(q), Some(a), m, Cop1(r))
          }
        }
    }
    val q0 = if (i == 0) Cop1(dfa.q0) else Cop2(0)
    new NSST[Q, A, B, X](
      states,
      base.in,
      base.variables,
      edges,
      q0,
      base.partialF
    ).renamed
  } // End of regexNSST

  /** Returns NSST that outputs the same string as input iff it meets constriant given by `dfas`.
    * That is, it reads input of the form w0#w1#...w(n-1)# (where n = dfas.length and # = None) and
    * outputs it if dfa(i) accepts w(i) for all i. */
  def regularNSST[Q, A](dfas: Seq[DFA[Q, A]], alphabet: Set[A]): NSST[Int, Option[A], Option[A], Int] = {
    assert(dfas.nonEmpty)
    type NQ = (Int, Q) // Represents DFA number by Int.
    type NA = Option[A]
    type X = Unit
    type Update = Concepts.Update[X, NA]
    type VarString = Concepts.Cupstar[X, NA]
    // Any update in the resulting NSST is one that just appends input character to variable ().
    val newAlphabet = alphabet.map[NA](Some.apply) + None
    val update: Map[NA, Update] =
      (newAlphabet).map(a => a -> Map(() -> List(Cop1(()), Cop2(a)))).toMap
    val (hd, tl) = (dfas.head, dfas.tail)
    val initialState = (0, hd.q0)
    var states: Set[NQ] = Set((0, hd.q0))
    var edges: List[(NQ, NA, Update, NQ)] = hd.transition
      .map[(NQ, NA, Update, NQ)] {
        case ((q, a), r) => ((0, q), Some(a), update(Some(a)), (0, r))
      }
      .toList
    var finalStates: Set[NQ] = hd.finalStates.map((0, _))
    for ((dfa, i) <- tl zip LazyList.from(1)) {
      states ++= dfa.states.map((i, _))
      edges ++:= finalStates.map(q => (q, None, update(None), (i, dfa.q0)))
      edges ++:= dfa.transition
        .map[(NQ, NA, Update, NQ)] {
          case ((q, a), r) => ((i, q), Some(a), update(Some(a)), (i, r))
        }
        .toList
      finalStates = dfa.finalStates.map((i, _))
    }
    val qf = (dfas.length, hd.q0) // hd.q0 can be any other value of type Q.
    states += qf
    edges ++= finalStates.map(q => (q, None, update(None), qf))
    val outF: Map[NQ, Set[VarString]] = Map(qf -> Set(List[Cop[Unit, NA]](Cop1(()))))
    new NSST[NQ, NA, NA, X](
      states,
      newAlphabet,
      Set(()),
      edges.toSet,
      initialState,
      outF
    ).renamed
  }

  /** Returns NSST which transduces a string of form "w0#...w(n-1)#" to
    * "w'0 ... w'(n-1)" where each length of w'(i) is equal to that of w(i) and
    * each w'(i) is made up of only one integer i. */
  def parikhNSST[C](n: Int, alpha: Set[C]): NSST[Int, Option[C], Int, Int] = {
    val states = Set.from(0 to n)
    type Q = Int
    type A = Option[C]
    type B = Int
    type X = Int
    type Update = Concepts.Update[X, B]
    type Edge = (Q, A, Update, Q)
    val edges: Iterable[Edge] = {
      val loop: Iterable[Edge] =
        for (q <- 0 until n; a <- alpha)
          yield (q, Some(a), Map(0 -> List(Cop1(0), Cop2(q))), q)
      val next: Iterable[Edge] =
        for (q <- 0 until n) yield ((q, None, Map(0 -> List(Cop1(0))), q + 1))
      loop ++ next
    }
    new NSST(
      states,
      alpha.map[Option[C]](Some.apply) + None,
      Set(0),
      edges.toSet,
      0,
      Map(n -> Set(List(Cop1(0))))
    )
  }

  import Constraint._
  def intVarsSL[A](constraint: SLConstraint[A]): Seq[IntVar] = {
    val SLConstraint(_, is, _) = constraint
    def inIE(ie: IntExp): Set[IntVar] = ie match {
      case VarExp(v)      => Set(v)
      case AddExp(es)     => es.toSet.flatMap(inIE)
      case SubExp(e1, e2) => inIE(e1) ++ inIE(e2)
      case _              => Set.empty
    }
    def inIC(ic: IntConstraint): Set[IntVar] = ic match {
      case IntEq(e1, e2) => inIE(e1) ++ inIE(e2)
      case IntLt(e1, e2) => inIE(e1) ++ inIE(e2)
      case IntConj(cs)   => cs.toSet.flatMap(inIC)
      case IntNeg(c)     => inIC(c)
    }
    inIC(IntConj(is)).toSeq
  }
  def stringVarsAtoms[A](as: Seq[AtomicConstraint[A]]): Seq[StringVar] = {
    def rhsVars(c: AtomicConstraint[A]): Seq[StringVar] = c match {
      case Constant(_, _)     => Nil
      case CatCstr(_, r1, r2) => List(r1, r2)
      case TransCstr(_, _, r) => List(r)
    }
    def lhsVar(c: AtomicConstraint[A]): StringVar = c match {
      case Constant(l, _)     => l
      case CatCstr(l, _, _)   => l
      case TransCstr(l, _, _) => l
    }
    val lhsVars = as.map(lhsVar)
    val notInLHS = as.toSet.flatMap(rhsVars).filterNot(lhsVars.contains).toSeq
    notInLHS ++ lhsVars
  }
  def stringVarsSL[A](c: SLConstraint[A]): Seq[StringVar] = {
    val SLConstraint(atoms, is, rs) = c
    val inAtoms = stringVarsAtoms(atoms)
    val notInAtoms = rs.map(_.v).filterNot(inAtoms.contains)
    inAtoms ++ notInAtoms
  }
  def usedAlphabetAtomic[A](c: AtomicConstraint[A]): Set[A] = c match {
    case Constant(_, word) => word.toSet
    case CatCstr(_, _, _)  => Set.empty
    case TransCstr(_, trans, _) =>
      trans match {
        case PrependAppend(pre, post) => (pre ++ post).toSet
        case ReplaceAll(target, word) => (target ++ word).toSet
        case Insert(_, word)          => word.toSet
        case At(_)                    => Set.empty
      }
  }
  def usedAlhpabetRegExp[A](re: RegExp[A]): Set[A] = re match {
    case EmptyExp | EpsExp => Set.empty
    case CharExp(c)        => Set(c)
    case CatExp(e1, e2)    => usedAlhpabetRegExp(e1) ++ usedAlhpabetRegExp(e2)
    case OrExp(e1, e2)     => usedAlhpabetRegExp(e1) ++ usedAlhpabetRegExp(e2)
    case StarExp(e)        => usedAlhpabetRegExp(e)
  }

  type SolverSST[A] = NSST[Int, Option[A], Option[A], Int]
  type ParikhNFT[A] = ENFT[Int, Option[A], Map[Int, Int]]

  /** Construct SST of constraint `c` assuming it is straight-line.
    * If `c` has integer constraints, this also construct an ε-NFA that outputs
    * vectors from variable number to length of its content. */
  def compileConstraint[A](c: SLConstraint[A], alphabet: Set[A]): (SolverSST[A], Option[ParikhNFT[A]]) = {
    val SLConstraint(atoms, is, rs) = c
    // If an input constriant is one like (z := x y; w := replaceall z "a" "b"; v in (a)*) then
    // its string variables are ordered like v, x, y, z, w (unused in atoms first).
    val stringVars = stringVarsSL(c)
    val ordering = stringVars.zipWithIndex.toMap
    // Construct SST from each atomic constraint.
    def compileAtomic(a: AtomicConstraint[A]): SolverSST[A] = a match {
      case Constant(l, w)     => ???
      case CatCstr(l, r1, r2) => concatNSST(ordering(l), ordering(r1), ordering(r2), alphabet)
      case TransCstr(l, t, r) =>
        t match {
          case PrependAppend(pre, post) => ???
          case ReplaceAll(target, word) => replaceAllNSST(target, word, ordering(l), ordering(r), alphabet)
          case Insert(pos, word)        => ???
          case At(pos)                  => ???
        }
    }
    val atomSSTs = atoms.map(compileAtomic)
    // Construct SST from regex constraint.
    val regexSST: SolverSST[A] = {
      def compileRE(re: RegExp[A]): DFA[Int, A] = new RegExp2NFA(re).construct().toDFA.renamed
      // Maps a string variable x to one DFA that accepts intersection of languages that x must belong to.
      val varToDFA = rs
        .groupMap(_.v)(_.re)
        .view
        .mapValues(res =>
          res.map(compileRE).reduce[DFA[Int, A]] { case (d1, d2) => (d1 intersect d2).renamed }.minimized
        )
        .toMap
        .withDefaultValue {
          // DFA that accepts all strings.
          new DFA[Int, A](
            Set(0),
            alphabet,
            alphabet.map(a => ((0, a), 0)).toMap,
            0,
            Set(0)
          )
        }
      // Sequence of DFAs in the order of string variables.
      val dfas = stringVars.map(varToDFA)
      regularNSST(dfas, alphabet)
    }
    val solverSST = (atomSSTs :+ regexSST).reduceRight(_ compose _)
    val parikhNFT =
      if (c.is.isEmpty) None
      else {
        val pSST = parikhNSST(stringVars.length, alphabet)
        Some((atomSSTs :+ regexSST).foldRight(pSST)(_ compose _).parikhEnft)
      }
    (solverSST, parikhNFT)
  }

  def getModelIfSat[A](c: SLConstraint[A], alphabet: Set[A]): Option[Map[StringVar, Seq[A]]] = {
    def witnessToModel(w: Seq[Option[A]]): Map[StringVar, List[A]] = {
      val valuation = w.foldRight[List[List[A]]](Nil) {
        case (None, acc)         => Nil :: acc
        case (Some(a), hd :: tl) => (a :: hd) :: tl
        case _                   => throw new Exception("This cannot happend.")
      }
      (stringVarsSL(c) zip valuation).toMap
    }
    compileConstraint(c, alphabet) match {
      // No integer constraint present
      case (sst, None) => {
        if (sst.isEmpty) None
        else {
          val input = sst.takeInput
          val witness = sst.transduce(input).head
          Some(witnessToModel(witness))
        }
      }
      // When c has integer constraint
      case (sst, Some(nft)) => {
        import com.microsoft.z3
        // i-th string variable will be named s"y$i"
        val parikhFormula: Parikh.Formula[String] = {
          import Parikh._
          type E = (Int, Image[Int], Int)
          type X = EnftVar[Int, Int, E]
          class Renamer() {
            var i = 0
            private def newVar() = {
              i += 1
              i
            }
            var eMap: Map[E, String] = Map.empty
            var qMap: Map[Int, String] = Map.empty
            def renamer(x: X): String = x match {
              case BNum(b) => s"y${b}"
              case ENum(e) => eMap.getOrElse(e, { val s = s"x${newVar()}"; eMap += e -> s; s })
              case Dist(q) => qMap.getOrElse(q, { val s = s"x${newVar()}"; qMap += q -> s; s })
            }
          }
          Formula.renameVars(Parikh.parikhEnftToPresburgerFormula(nft), new Renamer().renamer _)
        }
        val stringVars = stringVarsSL(c)
        // Parikh formula and positiveness of free variables are already added to solver.
        val (ctx, solver, stringVarsIntExpr) = {
          val cfg = new java.util.HashMap[String, String]()
          cfg.put("model", "true")
          val ctx = new z3.Context(cfg)
          val freeVars = (0 until stringVars.length).map(i => s"y$i").map(y => y -> ctx.mkIntConst(y))
          val stringVarsIntExpr = (stringVars zip freeVars).map { case (v, (_, e)) => v -> e }.toMap
          val zero = ctx.mkInt(0)
          val positives = freeVars.map { case (_, v) => ctx.mkGe(v, zero) }
          val expr = Parikh.Formula.formulaToExpr(ctx, freeVars.toMap, parikhFormula)
          val solver = ctx.mkSolver()
          solver.add(expr +: positives: _*)
          (ctx, solver, stringVarsIntExpr)
        }
        val intVars: Seq[IntVar] = intVarsSL(c)
        // Integer free variables' names start with 'z'
        val intVarIntExpr: Map[IntVar, z3.IntExpr] =
          intVars.map(v => v -> ctx.mkIntConst(s"z${v.name}")).toMap
        val intConstraints: Seq[z3.BoolExpr] = {
          def intExpToArithExp(ie: IntExp): z3.ArithExpr = ie match {
            case ConstExp(i)    => ctx.mkInt(i)
            case VarExp(v)      => intVarIntExpr(v)
            case LenExp(v)      => stringVarsIntExpr(v)
            case AddExp(es)     => ctx.mkAdd(es.toSeq.map(intExpToArithExp): _*)
            case SubExp(e1, e2) => ctx.mkSub(intExpToArithExp(e1), intExpToArithExp(e2))
          }
          def intConstraintToBoolExpr(ic: IntConstraint): z3.BoolExpr = ic match {
            case IntEq(e1, e2) => ctx.mkEq(intExpToArithExp(e1), intExpToArithExp(e2))
            case IntLt(e1, e2) => ctx.mkLt(intExpToArithExp(e1), intExpToArithExp(e2))
            case IntConj(cs)   => ctx.mkAnd(cs.toSeq.map(intConstraintToBoolExpr): _*)
            case IntNeg(c)     => ctx.mkNot(intConstraintToBoolExpr(c))
          }
          c.is.map(intConstraintToBoolExpr)
        }
        solver.add(intConstraints: _*)
        val res =
          if (solver.check() == z3.Status.SATISFIABLE) {
            val z3Model = solver.getModel()
            val stringVarsValue: Map[StringVar, Int] = stringVarsIntExpr.map {
              case (v, e) => v -> z3Model.eval(e, false).toString().toInt
            }
            // indexValue(i) == length of content of i-th string variable
            val indexValue: Map[Int, Int] = stringVars.zipWithIndex.map {
              case (v, i) => i -> stringVarsValue(v)
            }.toMap
            val input = nft.takeInputFor(indexValue, m => m.exists { case (a, i) => i > indexValue(a) })
            val witness = sst.transduce(input).head
            Some(witnessToModel(witness))
          } else None

        ctx.close()
        res

      }
    }
  }
}
