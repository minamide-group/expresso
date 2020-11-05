package com.github.kmn4.sst

import smtlib.trees._
import Commands._
import Terms._

import Constraint._
import Solver._
import cats.data.Writer
import cats.implicits._

class Solver(options: Solver.SolverOption) {

  sealed trait Mode
  case object StartMode extends Mode
  case object AssertMode extends Mode
  case object SatMode extends Mode
  case object UnsatMode extends Mode

  case class AssertionLevel(env: FunctionEnv, assertions: List[Terms.Term])

  var currentLogic: Option[Logic] = None
  var currentMode: Mode = StartMode

  /** This should never be empty */
  var assertionStack: List[AssertionLevel] = List(AssertionLevel(Map.empty, Nil))

  var sst: Option[Solver.SolverSST[Char]] = None
  var nft: Option[Solver.ParikhNFT[Char]] = None
  var currentModel: Option[Map[String, String]] = None

  def currentSL(): Either[String, SLConstraint[Char]] = {
    val AssertionLevel(env, assertions) :: tl = assertionStack
    try {
      val sl = assertions.foldLeft(SLConstraint[Char](Nil, Nil, Nil)) { (acc, term) =>
        expectConstraint(term, env) match {
          case Atom(a) => acc.copy(as = a +: acc.as)
          case IntC(i) => acc.copy(is = i +: acc.is)
          case REC(r)  => acc.copy(rs = r +: acc.rs)
        }
      }
      Right(sl)
    } catch {
      case e: Throwable => Left(e.toString())
    }
  }

  type Output = String
  val success = "success"

  type ExecutionResult = (Output, Mode)

  def currentFuncEnv: FunctionEnv = assertionStack.head.env
  def updateFunction(name: String, rank: Rank): Unit = {
    val hd :: tl = assertionStack
    assertionStack = hd.copy(env = hd.env + (name -> rank)) :: tl
  }
  def addFunction(name: String, rank: Rank): ExecutionResult = {
    if (currentFuncEnv.isDefinedAt(name)) ("(error \"name $name is already defined\")", AssertMode)
    else {
      updateFunction(name, rank)
      (success, AssertMode)
    }
  }

  /**
    * Execute `cmd` without printing output nor mode transition.
    * Other effects (e.g. pushing function to environment) take place within this function.
    *
    * @param cmd Command to be executed.
    * @return Solver response and next mode.
    */
  def execute(cmd: Command): ExecutionResult = cmd match {
    case SetLogic(logic) =>
      if (currentLogic.nonEmpty) ???
      else
        logic match {
          case NonStandardLogic(SSymbol("QF_S")) =>
            currentLogic = Some(logic)
            (success, AssertMode)
          case _ => ???
        }
    case DeclareConst(SSymbol(name), Sort(SimpleIdentifier(SSymbol(sortName)), Nil)) =>
      sortName match {
        case "Int"    => addFunction(name, IntConst)
        case "String" => addFunction(name, StringConst)
        case _        => ???
      }
    case DeclareFun(SSymbol(name), Nil, Sort(SimpleIdentifier(SSymbol(sortName)), Nil)) =>
      sortName match {
        case "Int"    => addFunction(name, IntConst)
        case "String" => addFunction(name, StringConst)
        case _        => ???
      }
    case Assert(term) =>
      val hd :: tl = assertionStack
      assertionStack = hd.copy(assertions = term :: hd.assertions) :: tl
      (success, AssertMode)
    case CheckSat() =>
      // TODO Seperate checking sat and getting model
      currentSL() match {
        case Right(sl) =>
          // Input / output alphabet is all characters that appears in given constraint + one additional char.
          // TODO Users should be able to specify a alphabet set.
          val alphabet = {
            import Solver._
            val Constraint.SLConstraint(atoms, is, rs) = sl
            val contained =
              (atoms.map(usedAlphabetAtomic) ++ rs.map(c => usedAlhpabetRegExp(c.re)))
                .fold(Set.empty)(_ union _)
            val printable = ' ' to '~'
            contained ++ printable.find(c => !contained.contains(c))
          }
          // val (sst, nft) = Solver.compileConstraint(sl, alphabet)
          val o = Solver
            .getModelIfSat(sl, alphabet)
            .map(model => model.map { case (Constraint.StringVar(name), value) => name -> value.mkString })
          currentModel = o
          o match {
            case None        => ("unsat", UnsatMode)
            case Some(model) => ("sat", SatMode)
          }
        case Left(msg) => println(msg); ???
      }
    case GetModel() =>
      currentMode match {
        case SatMode =>
          val s = currentModel.get
            .map { case (name, value) => s"""(define-fun $name () String "${value}")""" }
            .mkString("\n  ")
          (s"(model\n  $s\n)", SatMode)
        case _ => ???
      }
    case _ => ???
  }

  def executeTransPrint(cmd: Command): Unit = {
    val (output, mode) = execute(cmd)
    println(output)
    currentMode = mode
  }

  def executeTransPrint(script: Script): Unit = script.commands.foreach(executeTransPrint)
}

object Solver {
  case class Rank(args: List[Sort], res: Sort)
  val StringConst = Rank(Nil, Sort(SimpleIdentifier(SSymbol("String"))))
  val IntConst = Rank(Nil, Sort(SimpleIdentifier(SSymbol("Int"))))

  type FunctionEnv = Map[String, Rank]
  private sealed trait BoolExp
  private case class Atom(a: AtomicConstraint[Char]) extends BoolExp
  private case class IntC(i: IntConstraint) extends BoolExp
  private case class REC(r: RegexConstraint[Char]) extends BoolExp
  object SimpleQualID {
    def unapply(term: Term): Option[String] = term match {
      case QualifiedIdentifier(SimpleIdentifier(SSymbol(name)), None) => Some(name)
      case _                                                          => None
    }
  }
  object SimpleApp {
    def unapply(term: Term): Option[(String, Seq[Term])] = term match {
      case FunctionApplication(SimpleQualID(name), terms) => Some((name, terms))
      case _                                              => None
    }
  }
  private def expectTransduction(e: Term, env: FunctionEnv): (String, Transduction[Char]) = e match {
    case SimpleApp("str.replaceall", Seq(SimpleQualID(name), SString(target), SString(word)))
        if env(name) == StringConst =>
      (name, ReplaceAll(target, word))
    case SimpleApp("str.replace_some", Seq(SimpleQualID(name), SString(target), SString(word)))
        if env(name) == StringConst =>
      (name, ReplaceSome(target, word))
    case SimpleApp("str.at", Seq(SimpleQualID(name), SNumeral(pos))) if env(name) == StringConst =>
      (name, At(pos.toInt))
    case SimpleApp("str.insert", Seq(SimpleQualID(name), SNumeral(pos), SString(word)))
        if env(name) == StringConst =>
      (name, Insert(pos.toInt, word))
    case SimpleApp("str.reverse", Seq(SimpleQualID(name))) if env(name) == StringConst => (name, Reverse())
    case SimpleApp("str.substr", Seq(SimpleQualID(name), SNumeral(from), SNumeral(len))) =>
      (name, Substr(from.toInt, len.toInt))
    case SimpleApp("str.until_first", Seq(SimpleQualID(name), SString(target))) if env(name) == StringConst =>
      (name, UntilFirst(target))
    case _ => throw new Exception(s"${e.getPos}: Cannot interpret given S-expression as transduction: ${e}")
  }
  private def expectInt(e: Term, env: FunctionEnv): IntExp = e match {
    case SNumeral(i)                                 => ConstExp(i.toInt)
    case SimpleApp("-", Seq(e))                      => MinusExp(expectInt(e, env))
    case SimpleQualID(name) if env(name) == IntConst => VarExp(IntVar(name))
    case SimpleApp("str.len", Seq(SimpleQualID(name))) if env(name) == StringConst =>
      LenExp(StringVar(name))
    case SimpleApp("+", es)          => AddExp(es.map(expectInt(_, env)))
    case SimpleApp("-", Seq(e1, e2)) => SubExp(expectInt(e1, env), expectInt(e2, env))
    case _ =>
      throw new Exception(s"${e.getPos}: Cannot interpret given S-expression ${e} as int expression")
  }
  private def expectRegExp(e: Term): RegExp[Char] =
    e match {
      case SimpleApp("str.to.re", Seq(SString(s))) =>
        if (s.nonEmpty)
          s.map[RegExp[Char]](CharExp.apply).reduce[RegExp[Char]] { case (e1, e2) => CatExp(e1, e2) }
        else EpsExp
      case SimpleApp("re.*", Seq(e)) => StarExp(expectRegExp(e))
      case SimpleApp("re.+", Seq(e)) =>
        val re = expectRegExp(e)
        CatExp(re, StarExp(re))
      case SimpleApp("re.++", es) =>
        es.tail.foldLeft(expectRegExp(es.head)) { case (acc, e) => CatExp(acc, expectRegExp(e)) }
      case SimpleApp("re.union", es) =>
        es.tail.foldLeft(expectRegExp(es.head)) { case (acc, e) => OrExp(acc, expectRegExp(e)) }
      case SimpleApp("re.range", Seq(SString(c1), SString(c2))) if c1.length == 1 && c2.length == 1 =>
        throw new NotImplementedError("re.range is not implemented")
      case SimpleApp("re.comp", Seq(e)) => CompExp(expectRegExp(e))
      case SimpleQualID("re.allchar")   => DotExp
      case SimpleQualID("re.all")       => StarExp(DotExp)
      case _                            => throw new Exception(s"Cannot interpret given S-expression as regular expression: $e")
    }
  private def expectConstraint(e: Term, env: FunctionEnv): BoolExp = e match {
    case SimpleApp("=", Seq(SimpleQualID(name), SString(s))) if env(name) == StringConst =>
      Atom(Constant(StringVar(name), s))
    case SimpleApp("=", Seq(SimpleQualID(name), SimpleApp("str.++", rhs))) if rhs.forall {
          case SimpleQualID(name) => env(name) == StringConst
          case SString(s)         => true
          case _                  => false
        } =>
      Atom(CatCstr(StringVar(name), rhs.map {
        case SimpleQualID(name) => Right(StringVar(name))
        case SString(s)         => Left(s.toSeq)
      }))
    case SimpleApp("=", Seq(SimpleQualID(name), e)) if env(name) == StringConst =>
      val (rhs, trans) = expectTransduction(e, env)
      Atom(TransCstr(StringVar(name), trans, StringVar(rhs)))
    case SimpleApp("str.prefixof", Seq(SimpleQualID(lhs), SimpleQualID(rhs)))
        if env(lhs) == StringConst && env(rhs) == StringConst =>
      Atom(TransCstr(StringVar(lhs), TakePrefix(), StringVar(rhs)))
    case SimpleApp("str.suffixof", Seq(SimpleQualID(lhs), SimpleQualID(rhs)))
        if env(lhs) == StringConst && env(rhs) == StringConst =>
      Atom(TransCstr(StringVar(lhs), TakeSuffix(), StringVar(rhs)))
    case SimpleApp("=", Seq(e1, e2)) =>
      val i1 = expectInt(e1, env)
      val i2 = expectInt(e2, env)
      IntC(IntEq(i1, i2))
    case SimpleApp("<", Seq(e1, e2)) =>
      val i1 = expectInt(e1, env)
      val i2 = expectInt(e2, env)
      IntC(IntLt(i1, i2))
    case SimpleApp("<=", Seq(e1, e2)) =>
      val i1 = expectInt(e1, env)
      val i2 = expectInt(e2, env)
      IntC(IntNeg(IntLt(i2, i1)))
    case SimpleApp(">", Seq(e1, e2)) =>
      val i1 = expectInt(e1, env)
      val i2 = expectInt(e2, env)
      IntC(IntLt(i2, i1))
    case SimpleApp(">=", Seq(e1, e2)) =>
      val i1 = expectInt(e1, env)
      val i2 = expectInt(e2, env)
      IntC(IntNeg(IntLt(i1, i2)))
    case SimpleApp("not", Seq(e)) =>
      expectConstraint(e, env) match {
        case IntC(i) => IntC(IntNeg(i))
        case _       => throw new Exception(s"Not supported negation.")
      }
    case SimpleApp("and", es) =>
      val is = es.map(expectConstraint(_, env) match {
        case IntC(i) => i
        case _       => throw new Exception(s"Not supported conjunction.")
      })
      IntC(IntConj(is))
    case SimpleApp("or", es) =>
      val is = es.map(expectConstraint(_, env) match {
        case IntC(i) => i
        case _       => throw new Exception(s"Not supported disjunction.")
      })
      IntC(IntDisj(is))
    case SimpleApp("str.in.re", Seq(SimpleQualID(name), e)) if env(name) == StringConst =>
      REC(RegexConstraint(StringVar(name), expectRegExp(e)))
    case _ => throw new Exception(s"${e.getPos}: Cannot interpret given expression as of Bool sort: ${e}")
  }

  type SolverOption = Unit
  // Returns update which appends `w` to variable `x`, and is identity on other variables in `xs`.
  def appendWordTo[X, A](x: X, xs: Set[X], w: List[A]): Concepts.Update[X, A] =
    xs.map(y => y -> (List(Cop1(y)) ++ (if (y == x) w.map(Cop2(_)) else Nil))).toMap

  // Returns NSST whose states `q`s are embedded to Cop2(q).
  def embedStates2[P, Q, A, B, X](n: NSST[Q, A, B, X]): NSST[Cop[P, Q], A, B, X] = {
    n.copy(
      states = n.states.map(Cop2(_)),
      edges = n.edges.map { case (q, a, m, r) => (Cop2(q), a, m, Cop2(r)) },
      q0 = Cop2(n.q0),
      partialF = n.partialF.map { case (q, s) => Cop2(q) -> s }
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
    val inSet = (alphabet.map[Option[C]](Some(_))) + None
    val xs = otherVariables + inputVariable
    val outF: Map[Q, Set[Concepts.Cupstar[X, B]]] = Map((n, 0) -> Set(output))
    val updates = Concepts.updateMonoid(xs)
    type Edges = Set[(Q, A, Concepts.Update[X, B], Q)]
    val edges: Edges =
      for ((i, _) <- states; a <- inSet if i != n)
        yield (
          (i, 0),
          a,
          updates.unit + (inputVariable -> List(Cop1(inputVariable), Cop2(a))),
          (if (a == None) i + 1 else i, 0)
        )
    NSST(states, inSet, xs, edges, (0, 0), outF)
  }

  /** x(i) := word */
  def constantNSST[C](i: Int, word: Seq[C], alphabet: Set[C]): SolverSST[C] = {
    solverNsstTemplate(
      i,
      alphabet,
      (),
      Set.empty,
      List(Cop1(())) ++ word.map(a => Cop2(Some(a))) ++ List(Cop2(None))
    ).renamed
  }

  /** Construct DFA which accepts strings whose postfix is target.
    *  Each state i represents target.substring(0, i). */
  def postfixDFA[A](target: Seq[A], in: Set[A]): DFA[Int, A] = {
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

  /** Construct NSST which output concatenation of `rhs`.
    * Right(j) in `rhs` is `j`-th input delemited by #. */
  def concatNSST[C](i: Int, rhs: Seq[Either[Seq[C], Int]], alphabet: Set[C]): SolverSST[C] = {
    type Q = (Int, Int)
    trait X
    case object XIn extends X
    case class XJ(j: Int, id: Int) extends X
    val concated = rhs.zipWithIndex
      .flatMap[Cop[X, Option[C]]] {
        case (Left(as), _) => as.map(a => Cop2(Some(a)))
        case (Right(j), k) => Seq(Cop1(XJ(j, k)))
      }
      .toList
    val vars = concated.flatMap { case Cop1(x) => Some(x); case _ => None }
    val base =
      solverNsstTemplate(i, alphabet, XIn, vars.toSet, List(Cop1(XIn)) ++ concated ++ List(Cop2(None)))
    val edges = base.edges.map {
      case t @ ((q, 0), Some(a), m, (_, 0)) =>
        t.copy(_3 =
          m ++ vars
            .withFilter { case XJ(j, _) => j == q; case _ => false }
            .map(x => x -> List(Cop1(x), Cop2(Some(a))))
        )
      case other => other
    }
    base.copy(edges = edges).renamed
  }

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
    val newAlphabet = alphabet.map[NA](Some.apply) + None
    // Any update in the resulting NSST is one that just appends input character to variable ().
    val update: Map[NA, Update] =
      (newAlphabet).map(a => a -> Map(() -> List(Cop1(()), Cop2(a)))).toMap
    val (hd, tl) = (dfas.head, dfas.tail)
    val initialState = (0, hd.q0)
    var states: Set[NQ] = hd.states.map((0, _))
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
    NSST[NQ, NA, NA, X](
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
    NSST(
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
      case IntDisj(cs)   => cs.toSet.flatMap(inIC)
      case IntNeg(c)     => inIC(c)
    }
    inIC(IntConj(is)).toSeq
  }
  def stringVarsAtoms[A](as: Seq[AtomicConstraint[A]]): Seq[StringVar] = {
    def rhsVars(c: AtomicConstraint[A]): Seq[StringVar] = c match {
      case Constant(_, _)     => Nil
      case CatCstr(_, rhs)    => rhs.flatMap { case Right(v) => Some(v); case _ => None }
      case TransCstr(_, _, r) => List(r)
    }
    def lhsVar(c: AtomicConstraint[A]): StringVar = c match {
      case Constant(l, _)     => l
      case CatCstr(l, _)      => l
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
    case CatCstr(_, rhs)   => rhs.flatMap { case Left(s) => s; case _ => Seq.empty }.toSet
    case TransCstr(_, trans, _) =>
      trans match {
        case ReplaceAll(target, word)                                       => (target ++ word).toSet
        case ReplaceSome(target, word)                                      => (target ++ word).toSet
        case UntilFirst(target)                                             => target.toSet
        case Insert(_, word)                                                => word.toSet
        case At(_) | Reverse() | Substr(_, _) | TakePrefix() | TakeSuffix() => Set.empty
      }
  }
  def usedAlhpabetRegExp[A](re: RegExp[A]): Set[A] = re match {
    case EmptyExp | EpsExp | DotExp => Set.empty
    case CharExp(c)                 => Set(c)
    case CatExp(e1, e2)             => usedAlhpabetRegExp(e1) ++ usedAlhpabetRegExp(e2)
    case OrExp(e1, e2)              => usedAlhpabetRegExp(e1) ++ usedAlhpabetRegExp(e2)
    case StarExp(e)                 => usedAlhpabetRegExp(e)
    case CompExp(e)                 => usedAlhpabetRegExp(e)
  }

  type SolverSST[A] = NSST[Int, Option[A], Option[A], Int]
  type ParikhNFT[A] = ENFT[Int, Option[A], Map[Int, Int]]

  // Construct SST from each atomic constraint.
  def compileAtomic[A](alphabet: Set[A], ordering: Map[StringVar, Int])(
      a: AtomicConstraint[A]
  ): SolverSST[A] = a match {
    case Constant(l, word) => constantNSST(ordering(l), word, alphabet)
    case CatCstr(l, rhs)   => concatNSST(ordering(l), rhs.map(_.map(ordering)), alphabet)
    case TransCstr(l, t, r) =>
      val i = ordering(l)
      val j = ordering(r)
      t.toSolverSST(i, j, alphabet)
  }

  /** Construct SST of constraint `c` assuming it is straight-line.
    * If `c` has integer constraints, this also construct an ε-NFA that outputs
    * vectors from variable number to length of its content. */
  def compileConstraint[A](
      c: SLConstraint[A],
      alphabet: Set[A]
  ): (SolverSST[A], Option[ParikhNFT[A]]) = {
    val SLConstraint(atoms, is, rs) = c
    // If an input constriant is one like (z := x y; w := replaceall z "a" "b"; v in (a)*) then
    // its string variables are ordered like v, x, y, z, w (unused in atoms first).
    val stringVars = stringVarsSL(c)
    val ordering = stringVars.zipWithIndex.toMap
    val atomSSTs = atoms.map(compileAtomic(alphabet, ordering))
    // Construct SST from regex constraint.
    val regexSST: SolverSST[A] = {
      def compileRE(re: RegExp[A]): DFA[Int, A] = new RegExp2NFA(re, alphabet).construct().toDFA.renamed
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
    import scala.concurrent._
    import duration._
    import ExecutionContext.Implicits.global
    val ssts = atomSSTs :+ regexSST
    // TODO Find a way to safely cancel slower computation
    val solverSST = {
      // val right = {
      //   implicit val logger = new BufferedLogger
      //   Future { (atomSSTs :+ regexSST).reduceRight(_ compose _) }
      //     .map { sst =>
      //       println(s"## SOLVER RIGHT FOLDING FINISHED\n${logger.flushString}")
      //       sst
      //     }
      // }
      val right = Future.never
      val left = {
        implicit val logger = new BufferedLogger
        Future { (atomSSTs :+ regexSST).reduceLeft(_ compose _) }
          .map { sst =>
            println(s"## SOLVER LEFT FOLDING FINISHED\n${logger.flushString}")
            sst
          }
      }
      Future.firstCompletedOf(
        Iterable(
          right,
          left
        )
      )
    }
    val parikhNFT =
      if (c.is.isEmpty) Future { None }
      else {
        val pSST = parikhNSST(stringVars.length, alphabet)
        // val right = {
        //   implicit val logger = new BufferedLogger
        //   Future { Some((ssts.foldRight(pSST)(_ compose _).parikhEnft)) }
        //     .map { sst =>
        //       println(s"## PARIKH RIGHT FOLDING FINISHED\n${logger.flushString}")
        //       sst
        //     }
        // }
        val right = Future.never
        val left = {
          implicit val logger = new BufferedLogger
          Future { Some((ssts.reduceLeft[SolverSST[A]](_ compose _) compose pSST).parikhEnft) }
            .map { sst =>
              println(s"## PARIKH LEFT FOLDING FINISHED\n${logger.flushString}")
              sst
            }
        }
        Future.firstCompletedOf(
          Iterable(
            right,
            left
          )
        )
      }
    val mixed = for (sst <- solverSST; nft <- parikhNFT) yield (sst, nft)
    Await.result(
      mixed,
      Duration.Inf
    )
  }

  /** Get a model of constraint `c` if it is satisfiable.
    * `alphabet` is needed because set of alphabet may be specified by user,
    * thus cannot be determined from `c`. */
  def getModelIfSat[A](c: SLConstraint[A], alphabet: Set[A]): Option[Map[StringVar, Seq[A]]] = {
    def witnessToModel(w: Seq[Option[A]]): Map[StringVar, List[A]] = {
      val valuation = w.foldRight[List[List[A]]](Nil) {
        case (None, acc)         => Nil :: acc
        case (Some(a), hd :: tl) => (a :: hd) :: tl
        case _                   => throw new Exception("This cannot happen.")
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
            case MinusExp(e)    => ctx.mkUnaryMinus(intExpToArithExp(e))
          }
          def intConstraintToBoolExpr(ic: IntConstraint): z3.BoolExpr = ic match {
            case IntEq(e1, e2) => ctx.mkEq(intExpToArithExp(e1), intExpToArithExp(e2))
            case IntLt(e1, e2) => ctx.mkLt(intExpToArithExp(e1), intExpToArithExp(e2))
            case IntConj(cs)   => ctx.mkAnd(cs.toSeq.map(intConstraintToBoolExpr): _*)
            case IntDisj(cs)   => ctx.mkOr(cs.toSeq.map(intConstraintToBoolExpr): _*)
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
