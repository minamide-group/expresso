// TODO rename this file
package com.github.kmn4.sst

import com.microsoft.z3
import com.typesafe.scalalogging.Logger
import smtlib.theories.Ints
import smtlib.theories.experimental.Strings
import smtlib.theories.experimental.Strings.StringSort
import smtlib.theories.{Core => CoreTheory}
import smtlib.trees.Commands.{Command => SMTCommand}
import smtlib.trees.Terms.{SNumeral, SString, Sort, Term => SMTTerm}
import smtlib.trees.{Commands => SMTCommands}
import smtlib.trees.{Terms => SMTTerms}

import ParikhSolver._
import Presburger.Sugar._
import Constraint.Transduction
import Solver.{SimpleQualID, SimpleApp, SimpleTransduction, expectRegExp}
import com.github.kmn4.sst.experimental.ParikhRelation
import com.github.kmn4.sst.experimental.PST

class ParikhSolver(
    print: Boolean = false,
    logger: Logger = Logger("nop"),
    alphabet: Set[Char] = Set.empty // ADDED to the alphabet of constraints
) {

  def setLogic(logic: SMTCommands.Logic): Unit = ()

  // temp_*, len_*, user_*
  val freshTemp = {
    var varID = 0
    () => {
      varID += 1
      s"temp_$varID"
    }
  }

  var env = Map.empty[String, Sort]
  var constraints = Seq.empty[ParikhConstraint]

  def declareConst(name: SMTTerms.SSymbol, sort: SMTTerms.Sort): Unit = {
    val SMTTerms.SSymbol(s) = name
    sort match {
      case Ints.IntSort() | Strings.StringSort() => env += (s -> sort)
      case _                                     => throw new Exception(s"${sort.getPos}: Unsupported sort: ${sort}")
    }
  }

  def declareFun(name: SMTTerms.SSymbol, paramSorts: Seq[SMTTerms.Sort], returnSort: SMTTerms.Sort): Unit =
    paramSorts match {
      case Nil => declareConst(name, returnSort)
      case _   => throw new Exception(s"${name.getPos}: Only constants are supported")
    }

  def assert(assertion: SMTTerm): Unit = {
    val (c, cs) = expectConstraint(expandMacro(assertion))
    constraints ++= (cs :+ c)
  }

  class Checker(relGen: Iterator[SolverPR[Char, String]], idxVar: Seq[String]) {
    // pr の satisfialibity を確認
    // sat なら x_0, x_1, ... の値と i_0, i_1, ... の値を返す
    // 等式の左辺に現れる変数の値は返さないことに注意
    private def checkClause(pr: SolverPR[Char, String]): Option[(Seq[String], Map[String, Int])] = {
      // 共通部分をとる
      // 異なる文字列変数に対応する PA のログ変数がかぶらないようにする
      val psts: Seq[ParikhSST[Int, Char, Char, Unit, (Int /* index */, Int /* l */ ), String]] =
        pr.parikhAutomata.zipWithIndex.map {
          case (pas, idx) =>
            val pa = pas.map(_.pa).reduce[ParikhAutomaton[Int, Char, Int, String]] {
              case (p, q) => p.intersect(q).renamed
            }
            pa.toParikhSST.renamed(identity _, identity _, l => (idx, l))
        }
      // 整数変数 int_*, ログ変数 log_*_*, 束縛変数 bound_*
      val pstFormulas = psts.flatMap { pst =>
        val accept = pst.acceptFormula.renameVars {
          case Left(i)         => s"int_$i"
          case Right((idx, l)) => s"log_${idx}_$l"
        }
        val parikh = pst.parikhImageFormula.renameVars {
          case Left(b)         => s"bound_$b"
          case Right((idx, l)) => s"log_${idx}_$l"
        }
        Seq(accept, parikh)
      }
      val globalFormulas = pr.globalFormulas.map(_.renameVars(i => s"int_$i"))
      val formula = Presburger.Conj(pstFormulas ++ globalFormulas)
      withZ3Context { (ctx) =>
        val solver = ctx.mkSolver()
        val z3Expr = Presburger.Formula.formulaToZ3Expr(ctx, Map.empty[String, z3.IntExpr], formula)
        solver.add(z3Expr)
        if (solver.check() == z3.Status.SATISFIABLE) {
          val model = solver.getModel()
          def getValue(name: String): Int = model.eval(ctx.mkIntConst(name), false).toString().toInt
          // 得られたモデルの値を出力する入力文字列を探す
          val inputs = psts.map { pst =>
            val v = pst.ls.map { case il @ (idx, l) => il -> getValue(s"log_${idx}_$l") }.toMap
            pst.inputOutputFor(v)._1.mkString
          }
          // 整数変数のモデル
          val pat = "^int_(.*)".r
          val intVarValues = formula.freeVars.collect {
            case i @ pat(name) => name -> getValue(i)
          }
          Some((inputs, intVarValues.toMap))
        } else None
      }
    }
    def parseIntModel(iv: Map[String, Int]): Map[String, Int] =
      iv.collect { case (name, value) if name.indexOf("user_") == 0 => name.drop(5) -> value }
    val models = Cacher {
      for {
        rel <- relGen
        models <- checkClause(rel)
      } yield models
    }.getOrCalc _
    def checkSat(): Boolean = models().nonEmpty
    def getModel(): Option[(Map[String, String], Map[String, Int])] = models().nextOption().map {
      case (inputs, intVarValues) =>
        (inputs.zipWithIndex.map { case (s, idx) => idxVar(idx) -> s }.toMap, intVarValues)
    }
  }

  val (checker, resetChecker) = {
    val c = Cacher[Checker] {
      val (relGen, idxVar) = Compiler.compile(constraints, alphabet, logger)
      new Checker(relGen, idxVar)
    }
    (c.getOrCalc _, c.reset _)
  }

  def printLine(x: Any): Unit = if (print) println(x)

  def checkSat(): Unit = {
    val sat = checker().checkSat()
    logger.trace(s"checking done, ${if (sat) "SAT" else "UNSAT"}")
    if (sat) printLine("sat")
    else printLine("unsat")
  }

  def getModel(): Unit = {
    checker().getModel() match {
      case Some((sModel, iModel)) =>
        logger.trace(s"got model ${(sModel, iModel)}")
        for ((name, value) <- sModel) printLine(s"""(define-fun $name () String "${value}")""")
        for ((name, value) <- iModel) printLine(s"(define-fun $name () Int ${value})")
      case None => printLine("Cannot get model")
    }
  }

  def expandMacro(t: SMTTerm): SMTTerm = t match {
    case CoreTheory.Not(CoreTheory.Equals(SimpleQualID(s1), SimpleQualID(s2)))
        if env.get(s1).exists(_ == StringSort()) && env.get(s2).exists(_ == StringSort()) =>
      val (x, y) = (SimpleQualID(s1), SimpleQualID(s2))
      val i = SimpleQualID(freshTemp())
      // codeAt(x, i) != codeAt(y, i)
      CoreTheory.Not(CoreTheory.Equals(ParikhLanguage.CodeAt(x, i), ParikhLanguage.CodeAt(y, i)))
    case _ => t
  }

  // arbitrary int expression.
  // ex. (+ (str.indexof x "a" 0) 1) => Add(temp_i, 1), [x ∈ IndexOfFromZero("a", temp_i)]
  def expectInt(t: SMTTerm): (Presburger.Term[String], Seq[ParikhConstraint]) = {
    def parseAndAbstract(t: SMTTerm): (String, Seq[ParikhConstraint]) = {
      val (pt, cs) = expectInt(t)
      pt match {
        case Presburger.Var(s) => (s, cs)
        case _ => {
          val newVar = freshTemp()
          (newVar, cs :+ (Presburger.Var(newVar) === pt))
        }
      }
    }
    t match {
      case SNumeral(i)        => (Presburger.Const(i.toInt), Seq.empty)
      case SimpleQualID(name) => (Presburger.Var(s"user_$name"), Seq.empty)
      case Ints.Neg(t) =>
        val (pt, cs) = expectInt(t)
        (Presburger.Const(0) - pt, cs)
      case Strings.Length(SimpleQualID(name)) =>
        val lenVar = s"len_${name}"
        (Presburger.Var(lenVar), Seq(ParikhAssertion(name, ParikhLanguage.Length(lenVar))))
      case ParikhLanguage.CodeAt(SimpleQualID(name), i) if env.get(name).exists(_ == StringSort()) =>
        val c = freshTemp()
        val (j, cs) = parseAndAbstract(i)
        val assertion = ParikhAssertion(name, ParikhLanguage.CodeAt(j, c))
        (Presburger.Var(c), cs :+ assertion)
      case SimpleApp("+", ts) =>
        val (pts, css) = ts.map(expectInt).unzip
        (Presburger.Add(pts), css.flatten)
      case Ints.Sub(t1, t2) =>
        val (pt1, cs1) = expectInt(t1)
        val (pt2, cs2) = expectInt(t2)
        (Presburger.Sub(pt1, pt2), cs1 ++ cs2)
      case Strings.Experimental.IndexOf(SimpleQualID(name), SString(w), SNumeral(c)) if c == 0 =>
        val newVar = freshTemp()
        val constr = ParikhAssertion(name, ParikhLanguage.IndexOfConst(w, c.toInt, newVar))
        (Presburger.Var(newVar), Seq(constr))
      case Ints.Mul(SNumeral(c), t) =>
        val (pt, cs) = expectInt(t)
        (Presburger.Mult(Presburger.Const(c.toInt), pt), cs)
      case Strings.Experimental.IndexOf(SimpleQualID(name), SString(w), t) =>
        val (i, cs) = parseAndAbstract(t)
        val j = freshTemp()
        (Presburger.Var(j), cs :+ ParikhAssertion(name, ParikhLanguage.IndexOf(w, i, j)))
      case _ =>
        throw new Exception(s"${t.getPos}: Cannot interpret given S-expression ${t} as int expression")
    }
  }

  // (substr x t1 t2) where t1 or t2 is not numeral
  def expectParikhTransduction(
      t: SMTTerm
  ): (String, ParikhTransduction[Char, String], Seq[ParikhConstraint]) = t match {
    case Strings.Substring(SimpleQualID(rhsVar), t1, t2) =>
      val (pt1, cs1) = expectInt(t1)
      val (pt2, cs2) = expectInt(t2)
      val (from, len) = (freshTemp(), freshTemp())
      (
        rhsVar,
        ParikhTransduction.Substr(from, len),
        cs1 ++ cs2 ++ Seq(pt1 === Presburger.Var(from), pt2 === Presburger.Var(len))
      )
    case _ => throw new Exception(s"${t.getPos}: Cannot interpret given S-expression ${t} as transduction")
  }

  object IntConstraint {
    val binary = Seq[
      (
          smtlib.theories.Operations.Operation2,
          (Presburger.Term[String], Presburger.Term[String]) => Presburger.Formula[String]
      )
    ](
      (CoreTheory.Equals, Presburger.Eq.apply[String] _),
      (Ints.LessThan, Presburger.Lt.apply[String] _),
      (Ints.LessEquals, Presburger.Le.apply[String] _),
      (Ints.GreaterThan, Presburger.Gt _),
      (Ints.GreaterEquals, Presburger.Ge _)
    )
    def unapply(t: SMTTerm): Option[(PureIntConstraint, Seq[ParikhConstraint])] = {
      val binOpt = binary.find { case (op, _) => op.unapply(t).nonEmpty }.map {
        case (op, constructor) =>
          val Some((t1, t2)) = op.unapply(t)
          val (pt1, cs1) = expectInt(t1)
          val (pt2, cs2) = expectInt(t2)
          (constructor(pt1, pt2), cs1 ++ cs2)
      }
      if (binOpt.nonEmpty) return Some(binOpt.get)
      t match {
        case CoreTheory.Not(IntConstraint((f, cs))) => Some((Presburger.Not(f), cs))
        case CoreTheory.And(ts @ _*) =>
          val sub = ts.map(unapply)
          if (sub.exists(_.isEmpty)) return None
          val (fs, css) = sub.map(_.get).unzip
          Some((Presburger.Conj(fs), css.flatten))
        case CoreTheory.Or(ts @ _*) =>
          val sub = ts.map(unapply)
          if (sub.exists(_.isEmpty)) return None
          val (fs, css) = sub.map(_.get).unzip
          Some((Presburger.Disj(fs), css.flatten))
        case _ => None
      }
    }
  }

  object Concat {
    def unapply(t: SMTTerm): Option[Seq[Either[Seq[Char], String]]] = t match {
      case Strings.Concat(ts @ _*) if ts.forall {
            case SimpleQualID(_) | SString(_) => true
            case _                            => false
          } =>
        val wordAndVars = ts.collect {
          case SString(w)         => Left(w.toSeq)
          case SimpleQualID(name) => Right(name)
        }
        Some(wordAndVars)
      case _ => None
    }
  }

  // (assert t)
  // _1 is t, and _2 is int equations and / or Parick assertions (for length).
  def expectConstraint(t: SMTTerm): (ParikhConstraint, Seq[ParikhConstraint]) = t match {
    // If (= x t) and x is string variable then t is transduction
    case CoreTheory.Equals(SimpleQualID(name), t) if env(name) == Strings.StringSort() =>
      t match {
        case SimpleTransduction(rhsStringVar, trans) =>
          (ParikhAssignment(name, trans, rhsStringVar), Seq.empty)
        case Concat(wordAndVars) => (CatAssignment(name, wordAndVars), Seq.empty)
        case _ =>
          val (rhs, trans, cs) = expectParikhTransduction(t)
          (ParikhAssignment(name, trans, rhs), cs)
      }
    // Other equalities are between ints.
    case IntConstraint(f, cs) => (f, cs)
    case Strings.InRegex(SimpleQualID(name), t) =>
      val re = expectRegExp(t)
      (ParikhAssertion(name, re), Seq.empty)
    case _ => throw new Exception(s"${t.getPos}: Unsupported assertion: ${t}")
  }

  def execute(cmd: SMTCommand): Unit = cmd match {
    case SMTCommands.SetLogic(logic)                          => setLogic(logic)
    case SMTCommands.DeclareConst(name, sort)                 => declareConst(name, sort)
    case SMTCommands.DeclareFun(name, paramSorts, returnSort) => declareFun(name, paramSorts, returnSort)
    case SMTCommands.Assert(assertion)                        => assert(assertion)
    case SMTCommands.CheckSat()                               => checkSat()
    case SMTCommands.GetModel()                               => getModel()
    case _                                                    => throw new Exception(s"${cmd.getPos}: Unsupported command: ${cmd}")
  }

  def executeScript(script: smtlib.trees.Commands.Script): Unit = script.commands.foreach(execute)
}

object ParikhSolver {
  case class SolverOption(print: Boolean = true, logger: Logger = Logger("nop"))

  type SolverPSST[C, I] = ParikhSST[Int, Option[C], Option[C], Int, Int, I]
  type SolverPR[C, I] = ParikhRelation[Int, C, Int, I]

  sealed trait ParikhLanguage[C, I] {
    def toParikhAutomaton(alphabet: Set[C]): ParikhAutomaton[Int, C, Int, I]
    def usedAlphabet: Set[C]
  }

  object ParikhLanguage {
    implicit class FromRegExp[C, I](val re: RegExp[C]) extends ParikhLanguage[C, I] {

      def usedAlphabet: Set[C] = re.usedAlphabet

      def toParikhAutomaton(alphabet: Set[C]): ParikhAutomaton[Int, C, Int, I] =
        re.toNFA(alphabet).toDFA.toParikhAutomaton.renamed
    }
    case class Length[A, I](lenVar: I) extends ParikhLanguage[A, I] {
      def usedAlphabet: Set[A] = Set.empty

      def toParikhAutomaton(alphabet: Set[A]): ParikhAutomaton[Int, A, Int, I] =
        ParikhAutomaton(
          Set(0),
          alphabet,
          Set(0),
          Set(lenVar),
          alphabet.map(a => (0, a, Map(0 -> 1), 0)),
          0,
          Set((0, Map(0 -> 0))),
          Seq(Presburger.Eq(Presburger.Var(Left(lenVar)), Presburger.Var(Right(0))))
        )
    }

    // (= j (str.indexof x w c)) --> IndexOfConst(w, c, j)
    case class IndexOfConst[A, I](target: Seq[A], from: Int, jName: I) extends ParikhLanguage[A, I] {
      def usedAlphabet: Set[A] = target.toSet

      def toParikhAutomaton(alphabet: Set[A]): ParikhAutomaton[Int, A, Int, I] = {
        import Presburger._
        type L = Int
        type T = Term[Either[I, L]]
        val j: T = Var(Left(jName))
        val input: T = Var(Right(0))
        val untilMatch: T = Var(Right(1))
        type Q = Int
        type Edges = Iterable[(Q, A, Map[L, Int], Q)]
        val dfa = Solver.postfixDFA(target, alphabet)
        val skipStates = (-from to -1).toSet
        val skipEdges = for {
          q <- skipStates
          a <- alphabet
        } yield (q, a, Map(0 -> 1, 1 -> 1), q + 1)
        val skipOutGraph = skipStates.map(q => (q, Map(0 -> 0, 1 -> 0)))
        val states = dfa.states
        val edges: Edges = {
          for {
            q <- states
            a <- alphabet
          } yield {
            val r = dfa.transition.getOrElse((q, a), q)
            val skipped =
              if (dfa.finalStates(r)) 0
              else q + 1 - r
            val v = Map(0 -> 1, 1 -> skipped)
            (q, a, v, r)
          }
        }
        val outGraph =
          // On each state q, DFA has partially matched prefix of target string.
          states.map(q => (q, Map(0 -> 0, 1 -> (q % target.length))))
        val acceptFormulas = Seq(
          (input < from || input <= untilMatch) ==> (j === -1),
          (input >= from && input > untilMatch) ==> (j === untilMatch)
        )
        ParikhAutomaton[Q, A, L, I](
          states ++ skipStates,
          alphabet,
          Set(0, 1),
          Set(jName),
          edges.toSet ++ skipEdges,
          -from,
          outGraph ++ skipOutGraph,
          acceptFormulas
        )
      }
    }

    // (= j (str.indexof x w i)) --> x ∈ IndexOf(w, i, j)
    case class IndexOf[A, I](target: Seq[A], iName: I, jName: I) extends ParikhLanguage[A, I] {
      def usedAlphabet: Set[A] = target.toSet

      def toParikhAutomaton(alphabet: Set[A]): ParikhAutomaton[Int, A, Int, I] = {
        import Presburger._
        type L = Int
        type T = Term[Either[I, L]]
        val i: T = Var(Left(iName))
        val j: T = Var(Left(jName))
        val input: T = Var(Right(0))
        val untilMatch: T = Var(Right(1))
        val skipped: T = Var(Right(2))
        type Q = Int
        type Edges = Iterable[(Q, A, Map[L, Int], Q)]
        val dfa = Solver.postfixDFA(target, alphabet)
        val states = dfa.states
        val edges: Edges = {
          for {
            q <- states
            a <- alphabet
          } yield {
            val r = dfa.transition.getOrElse((q, a), q)
            val skipped =
              if (dfa.finalStates(r)) 0
              else q + 1 - r
            val v = Map(0 -> 1, 1 -> skipped, 2 -> 0)
            (q, a, v, r)
          }
        }
        val outGraph =
          // On each state q, DFA has partially matched prefix of target string.
          states.map(q => (q, Map(0 -> 0, 1 -> (q % target.length), 2 -> 0)))
        val acceptFormulas = Seq(
          skipped === i,
          (input <= untilMatch) ==> (j === -1),
          (input > untilMatch) ==> (j === untilMatch)
        )
        val skipState = -1
        val fromSkipState = {
          val trans = graphToMap(edges) { case (q, a, v, r) => (q, a) -> (r, v) }
          alphabet.flatMap { a =>
            trans(dfa.q0, a).map { case (r, v) => (skipState, a, v + (2 -> 0), r) } +
              ((skipState, a, Map(0 -> 1, 1 -> 1, 2 -> 1), dfa.q0))
          }
        }
        ParikhAutomaton[Q, A, L, I](
          states + skipState,
          alphabet,
          Set(0, 1, 2),
          Set(iName, jName),
          edges.toSet ++ fromSkipState,
          skipState,
          outGraph + ((skipState, Map(0 -> 0, 1 -> 0, 2 -> 0))),
          acceptFormulas
        )
      }
    }
    case class CodeAt[I](iName: I, cName: I) extends ParikhLanguage[Char, I] {
      def usedAlphabet: Set[Char] = Set.empty
      def toParikhAutomaton(alphabet: Set[Char]): ParikhAutomaton[Int, Char, Int, I] = {
        import Presburger._
        val (q0, qf) = (0, 1)
        type T = Term[Either[I, Int]]
        val (i, c): (T, T) = (Var(Left(iName)), Var(Left(cName)))
        val (input, index, code): (T, T, T) = (Var(Right(0)), Var(Right(1)), Var(Right(2)))
        ParikhAutomaton(
          Set(q0, qf),
          alphabet,
          Set(0, 1, 2),
          Set(iName, cName),
          alphabet.flatMap { a =>
            Iterable(
              (q0, a, Map(0 -> 1, 1 -> 1, 2 -> 0), q0),
              (q0, a, Map(0 -> 1, 1 -> 0, 2 -> a.toInt), qf),
              (qf, a, Map(0 -> 1, 1 -> 0, 2 -> 0), qf)
            )
          },
          q0,
          Set((q0, Map(0 -> 0, 1 -> 0, 2 -> -1)), (qf, Map(0 -> 0, 1 -> 0, 2 -> 0))),
          Seq(
            (i >= 0 && i < input) ==> (i === index && c === code),
            (i < 0 || input <= i) ==> (c === -1)
          )
        )
      }
    }

    object CodeAt {
      def apply(x: SMTTerm, i: SMTTerm): SMTTerm = SimpleApp("code_at", x, i)
      def unapply(t: SMTTerm): Option[(SMTTerm, SMTTerm)] = t match {
        case SimpleApp("code_at", Seq(x, i)) => Some(x, i)
        case _                               => None
      }
    }
  }

  trait ParikhTransduction[C, I] {
    def usedAlphabet: Set[C]
    def toParikhSST(alphabet: Set[C]): ParikhSST[Int, C, C, Int, Int, I]
    def toSolverPSST(alphabet: Set[C], lhsStringVarIdx: Int, rhsStringVarIdx: Int): SolverPSST[C, I] = {
      sealed trait X
      case object XIn extends X
      case class XJ(x: Int) extends X
      type Q = (Int, Int)
      type A = Option[C]
      type UpdateX = Update[X, A]
      type UpdateL = Map[Int, Int]
      type Edges = Iterable[(Q, A, UpdateX, UpdateL, Q)]
      val j = rhsStringVarIdx
      val jsst = this.toParikhSST(alphabet)
      val xjs: Set[X] = jsst.xs.map(XJ.apply)
      val xj = xjs.head
      val base =
        Solver
          .solverNsstTemplate[C, X](
            lhsStringVarIdx,
            alphabet,
            XIn,
            xjs,
            List(Cop1(XIn), Cop1(xj), Cop2(None))
          )
          .toParikhSST[Int, I](jsst.ls)
      val xs = base.xs
      val updates: Monoid[UpdateX] = updateMonoid(xs)
      val states: Set[Q] = base.states - ((j, 0)) ++ jsst.states.map((j, _))
      val edges: Edges = {
        val baseNoJ = base.edges.filter {
          case (q, a, m, v, r) => (q._1 != j) && (r._1 != j)
        }
        def unit(a: A): UpdateX = updates.unit + (XIn -> List(Cop1(XIn), Cop2(a)))
        def reset(a: A): UpdateX = xs.map(_ -> Nil).toMap + (XIn -> List(Cop1(XIn), Cop2(a)))
        val toJ =
          ((j - 1, 0), None, unit(None), jsst.ls.map(_ -> 0).toMap, (j, jsst.q0))
        def embedList(l: Cupstar[Int, C]): Cupstar[X, A] = l.map(_.map1(XJ.apply)).map(_.map2(Option.apply))
        def embedUpdate(m: Update[Int, C]): Update[X, A] = m.map { case (x, l) => XJ(x) -> embedList(l) }
        val withinJ: Edges = jsst.edges.map {
          case (q, a, m, v, r) =>
            (((j, q), Some(a), embedUpdate(m) + (XIn -> List(Cop1(XIn), Cop2(Some(a)))), v, (j, r)))
        }
        val fromJ: Edges =
          for ((qf, s) <- jsst.outF; (l, v) <- s)
            yield ((j, qf), None, reset(None) + (xj -> embedList(l)), v, (j + 1, 0))

        baseNoJ + toJ ++ withinJ ++ fromJ
      }

      ParikhSST[Q, A, A, X, Int, I](
        states,
        base.inSet,
        xs ++ xjs,
        jsst.ls,
        jsst.is,
        edges.toSet,
        if (j == 0) (j, jsst.q0) else (0, 0),
        base.outGraph,
        jsst.acceptFormulas
      ).renamed
    }
  }

  object ParikhTransduction {
    implicit class NSSTTransductionIsParikhTransduction[C, I](trans: Transduction[C])
        extends ParikhTransduction[C, I] {
      def usedAlphabet: Set[C] = trans.usedAlphabet

      def toParikhSST(alphabet: Set[C]): ParikhSST[Int, C, C, Int, Int, I] =
        trans.toSST(alphabet).toParikhSST

    }

    case class Substr[A, I](idxName: I, lenName: I) extends ParikhTransduction[A, I] {

      def usedAlphabet: Set[A] = Set.empty

      def toParikhSST(alphabet: Set[A]): ParikhSST[Int, A, A, Int, Int, I] = {
        import Presburger._
        val X = 0
        type T = Term[Either[I, Int]]
        val idx: T = Var(Left(idxName))
        val len: T = Var(Left(lenName))
        val input: T = Var(Right(0))
        val taken: T = Var(Right(1))
        val sought: T = Var(Right(2))
        val unit @ (unitX, unitL): (Update[Int, A], ParikhSST.ParikhUpdate[Int]) =
          (Map(X -> List(Cop1(X))), Map(0 -> 1, 1 -> 0, 2 -> 0))
        val edges = alphabet
          .flatMap { a =>
            val seek = (unitX, unitL + (2 -> 1))
            val take = (Map(X -> List(Cop1(X), Cop2(a))), unitL + (1 -> 1))
            val ignore = unit
            Iterable(
              (0, a, seek, 0),
              (0, a, take, 1),
              (1, a, take, 1),
              (1, a, ignore, 2),
              (2, a, ignore, 2)
            )
          }
          .map { case (q, a, (mx, mh), r) => (q, a, mx, mh, r) }
        val acceptFormulas = {
          val idxOutOrNegLen = idx < 0 || idx >= input || len <= 0
          Seq(
            idxOutOrNegLen ==> (taken === 0),
            (!idxOutOrNegLen && len <= input - idx) ==> (sought === idx && taken === len),
            (!idxOutOrNegLen && len > input - idx) ==> (sought === idx && taken === input - idx)
          )
        }
        ParikhSST[Int, A, A, Int, Int, I](
          Set(0, 1, 2),
          alphabet,
          Set(X),
          Set(0, 1, 2),
          Set(idxName, lenName),
          edges,
          0,
          (0 to 2).map((_, List(Cop1(X)), (0 to 2).map(_ -> 0).toMap)).toSet,
          acceptFormulas
        )
      }
    }
  }

  sealed trait ParikhConstraint {
    def usedAlphabet: Set[Char]
    def dependerVars: Seq[String]
    def dependeeVars: Seq[String]
  }
  sealed trait AtomicAssignment extends ParikhConstraint {
    def lhsStringVar: String
    def toSolverPSST(varIdx: Map[String, Int])(alphabet: Set[Char]): SolverPSST[Char, String]
    def toExpPST(alphabet: Set[Char]): experimental.PST

    def dependerVars: Seq[String] = Seq(lhsStringVar)
  }
  case class ParikhAssignment(
      lhsStringVar: String,
      trans: ParikhTransduction[Char, String],
      rhsStringVar: String
  ) extends AtomicAssignment {

    override def toExpPST(alphabet: Set[Char]): PST = {
      val psst = trans.toParikhSST(alphabet)
      psst.copy(
        inSet = psst.inSet.map(Left.apply),
        edges = psst.edges.map(e => e.copy(_2 = Left(e._2)))
      )
    }

    override def dependerVars: Seq[String] = Seq(lhsStringVar)

    override def dependeeVars: Seq[String] = Seq(rhsStringVar)

    def usedAlphabet: Set[Char] = trans.usedAlphabet
    def toSolverPSST(varIdx: Map[String, Int])(alphabet: Set[Char]): SolverPSST[Char, String] =
      trans.toSolverPSST(alphabet, varIdx(lhsStringVar), varIdx(rhsStringVar))
  }
  // Left(word), Right(stringVar)
  case class CatAssignment(lhsStringVar: String, wordAndVars: Seq[Either[Seq[Char], String]])
      extends AtomicAssignment {

    // TODO wordsAndVars が少なくとも1つの文字列変数を含むことを仮定している点を緩和
    override def toExpPST(alphabet: Set[Char]): PST = {
      type Q = Int
      type A = Either[Char, Int]
      type B = Char
      type X = Unit
      type E = NSST.Edge[Q, A, B, X]
      type O = NSST.Out[Q, X, B]
      val depSize: Int = dependeeVars.size
      val states: Set[Q] = (0 until depSize).toSet
      val inSet: Set[A] = alphabet.map(Left.apply) ++ (0 to depSize - 2).map(Right.apply).toSet
      // w0 x0 w1 ... wn-1 xn-1 wn のときの w0 ... wn
      val words: Seq[Seq[Char]] = {
        wordAndVars.foldRight(List(Seq.empty[B])) {
          case (Left(s), h :: rst) => (s ++ h) :: rst
          case (Right(_), acc)     => Nil :: acc
          case _                   => throw new Exception("This cannot be the case")
        }
      }
      val edges: Set[E] = {
        val loop: Iterable[E] =
          for {
            i <- 0 to depSize - 1
            a <- alphabet
          } yield {
            val adding = List(Cop1(()), Cop2(a))
            val m = Map(() -> adding)
            (i, Left(a), m, i)
          }
        val next: Iterable[E] =
          (0 to depSize - 2).map { i =>
            val xbs = Cop1(()) :: words(i + 1).map(Cop2.apply).toList
            val m = Map(() -> xbs)
            (i, Right(i), m, i + 1)
          }
        (loop ++ next).toSet
      }
      val outGraph: Set[O] = {
        val added: Cupstar[X, B] =
          (words(0).map(Cop2.apply) ++ Seq(Cop1(())) ++ words.last.map(Cop2.apply)).toList
        Set((depSize - 1, added))
      }
      NSST(
        states,
        inSet,
        Set(()),
        edges,
        0,
        graphToMap(outGraph)(identity)
      ).renamed.toParikhSST
    }

    override def dependerVars: Seq[String] = Seq(lhsStringVar)

    override def dependeeVars: Seq[String] = wordAndVars.flatMap(_.toOption)

    def usedAlphabet: Set[Char] = wordAndVars.flatMap(_.left.getOrElse(Set.empty)).toSet
    def toSolverPSST(varIdx: Map[String, Int])(alphabet: Set[Char]): SolverPSST[Char, String] =
      Solver.concatNSST(varIdx(lhsStringVar), wordAndVars.map(_.map(varIdx)), alphabet).toParikhSST
  }
  case class ParikhAssertion(stringVar: String, lang: ParikhLanguage[Char, String]) extends ParikhConstraint {

    override def dependerVars: Seq[String] = Seq.empty

    override def dependeeVars: Seq[String] = Seq(stringVar)

    def usedAlphabet: Set[Char] = lang.usedAlphabet
  }
  type PureIntConstraint = Presburger.Formula[String]
  implicit class IntConstraintIsParikhConstraint(val formula: PureIntConstraint) extends ParikhConstraint {

    override def dependerVars: Seq[String] = Seq.empty

    override def dependeeVars: Seq[String] = Seq.empty

    def usedAlphabet: Set[Char] = Set.empty

  }
  object IntConstraintIsParikhConstraint {
    def unapply(c: ParikhConstraint): Option[PureIntConstraint] = c match {
      case (c: IntConstraintIsParikhConstraint) => Some(c.formula)
      case _                                    => None
    }
  }

  object Compiler {
    def stringVarIndex(constraints: Seq[ParikhConstraint]): Seq[(String, Int)] = {
      val dependers = constraints.flatMap(_.dependerVars).distinct
      val dependees = constraints.flatMap(_.dependeeVars).distinct
      val independents = dependees.diff(dependers)
      (independents ++ dependers).distinct.zipWithIndex
    }

    /** Returns ParikhAutomaton that accepts an input iff it meets constriant given by `pas`.
      * That is, it reads an input of the form w0#w1#...w(n-1)# (where n = dfas.length and # = None) and
      * accepts if pas(i) accepts w(i) for all i. */
    def solverPA[Q, A, L, I](
        pas: Seq[ParikhAutomaton[Q, A, L, I]], // ordered by corresponding string variables.
        q: Q // this will be used as "default state", and any value of type Q will suffice.
    ): ParikhAutomaton[(Int, Q), Option[A], (Int, L), I] = {
      type NQ = (Int, Q) // Represents PA number by Int.
      type NA = Option[A]
      type NL = (Int, L)
      type UpdateL = Map[L, Int]
      type UpdateNL = Map[NL, Int]
      val ls = for {
        (pa, i) <- pas.zipWithIndex
        l <- pa.ls
      } yield (i, l)
      def update(v: UpdateL, i: Int): UpdateNL =
        ls.map {
          case nl @ (j, l) if j == i => nl -> v(l)
          case nl                    => nl -> 0
        }.toMap
      val initialState = (0, pas.headOption.map(_.q0).getOrElse(q))
      var states: Set[NQ] = Set.empty
      var edges: List[(NQ, NA, UpdateNL, NQ)] = Nil
      var acceptRelation: Set[(NQ, UpdateNL)] = Set.empty
      for ((pa, i) <- pas.zipWithIndex) {
        states ++= pa.states.map((i, _))
        edges ++:= acceptRelation.map { case (q, v) => (q, None, v, (i, pa.q0)) }
        edges ++:= pa.edges
          .map[(NQ, NA, UpdateNL, NQ)] { case (q, a, v, r) => ((i, q), Some(a), update(v, i), (i, r)) }
          .toList
        acceptRelation = pa.acceptRelation.map { case (q, v) => ((i, q), update(v, i)) }
      }
      val qf = (pas.length, q)
      states += qf
      edges ++= acceptRelation.map { case (q, v) => (q, None, v, qf) }
      val acceptFormulas = for {
        (pa, i) <- pas.zipWithIndex
        f <- pa.acceptFormulas
      } yield f.renameVars(_.map((i, _)))
      ParikhAutomaton[NQ, NA, NL, I](
        states,
        addNone(pas.flatMap(_.inSet).toSet),
        ls.toSet,
        pas.flatMap(_.is).toSet,
        edges.toSet,
        initialState,
        Set((qf, ls.map(_ -> 0).toMap)),
        acceptFormulas
      )
    }

    def compileParikhAssertions(
        assertions: Map[Int, Seq[ParikhLanguage[Char, String]]],
        alphabet: Set[Char],
        lastVarIdx: Int
    ): SolverPSST[Char, String] = {
      require(
        assertions.isEmpty || lastVarIdx >= assertions.map(_._1).max,
        "All LHS of PA assertions should be less than or equal to max LHS of assignments."
      )
      val idxRegularsParikhs = {
        assertions.map {
          case (i, langs) =>
            val rs = langs.collect { case (l: ParikhLanguage.FromRegExp[Char, String]) => l.re }
            val ps = langs.filterNot(_.isInstanceOf[ParikhLanguage.FromRegExp[Char, String]])
            i -> (rs, ps)
        }
      }
      val idxPA = idxRegularsParikhs.view.mapValues {
        case (rs, ps) =>
          val dfas = rs.map(_.toNFA(alphabet).toDFA.minimized)
          val dfa = dfas
            .fold[DFA[Int, Char]](DFA.universal(0, alphabet)) { case (d1, d2) => (d1 intersect d2).renamed }
            .minimized
          val pa = ps
            .map(_.toParikhAutomaton(alphabet))
            .fold[ParikhAutomaton[Int, Char, Int, String]](ParikhAutomaton.universal(0, alphabet)) {
              case (p1, p2) => (p1 intersect p2).renamed
            }
          (dfa.toParikhAutomaton intersect pa).renamed
      }
      // (i, j) -- state j of a PSST of i-th string variable
      val inSet = addNone(alphabet)
      val universalPA = ParikhAutomaton.universal[Int, Char, Int, String](0, alphabet)
      solverPA((0 to lastVarIdx).map(idxPA.getOrElse(_, universalPA)), 0).toParikhSST.renamed
    }

    // TODO この名前だと Hoare 論理のアレみたいで misleading なので変える
    case class Triple(
        assignments: Seq[(Int, Set[Char] => experimental.PST, Seq[Int])], // (左辺, PST, 右辺)
        assertions: Map[Int, Seq[ParikhLanguage[Char, String]]], // [string var idx] in [Parikh langs]
        arithFormulas: Seq[PureIntConstraint] // formula over int variables
    ) {
      // 文字列変数の添字の最大値
      def maxStringVarOption: Option[Int] = {
        val iter1 = assignments.iterator.map(_._1)
        val iter2 = assertions.iterator.map(_._1)
        (iter1 ++ iter2).maxOption
      }

      // 文字列変数の添字の最大値
      // なお，assignments が非空ならその最後のインデックスに一致するはず
      def maxStringVar: Int = maxStringVarOption.get
    }

    case class PreImagable(pst: experimental.PST, rhs: Seq[Int])

    // 条件: transductions は lhs について昇順
    // 条件: relation の PA は lhs について昇順で，0 から順にならぶ
    case class Configuration(
        transductions: Seq[PreImagable],
        relation: ParikhRelation[Int, Char, Int, String]
    )

    // トランスダクション，言語，整数制約を PST と PR にまとめる
    // NOTE assignments は左辺変数でソート済みと仮定
    def organize(triple: Triple, alphabet: Set[Char]): Configuration = {
      val Triple(assignments, assertions, _) = triple
      val maxVar = triple.maxStringVar
      // assignments から PST を構成
      val transes = assignments.map {
        case (_, trans, rhs) =>
          val pst = trans(alphabet)
          PreImagable(pst, rhs)
      }
      // assertions と arithFormulas から PR が得られる
      val rel = {
        val pas = (0 to maxVar).map { idx =>
          val all = ParikhAutomaton.universal[Int, Char, Int, String](0, alphabet)
          assertions.getOrElse(idx, Seq.empty).foldLeft(all) {
            case (acc, lang) => acc.intersect(lang.toParikhAutomaton(alphabet)).renamed
          }
        }
        val withID = pas.zipWithIndex.map {
          case (pa, idx) =>
            Seq(experimental.IdentifiedPA(idx, pa))
        }
        ParikhRelation(withID, triple.arithFormulas)
      }
      Configuration(transes, rel)
    }

    // transductions が非空である間 relation の逆像を計算する
    // disjunction が現れると非決定的な選択をする．この非決定性は Iterator が表している．
    def iteratePreImage(config: Configuration): Iterator[ParikhRelation[Int, Char, Int, String]] = {
      import experimental.Transduction._
      val Configuration(ts, rel) = config
      ts.foldRight(LazyList(rel)) {
          case (PreImagable(pst, rhs), acc) =>
            type PA = experimental.IdentifiedPA[Int, Char, Int, String]
            // next() すると pst^-1(lang) から1つずつ選んだ組を返す
            // TODO PR において各変数の言語が単一の PA で表されればにここは不要になる
            def clauseChoices(
                langs: LazyList[PA],
                maxID: Int
            ): Iterator[Seq[(Seq[PA], experimental.GlobalFormulas[String])]] = {
              val idInc = rhs.length // maxID は逆像をとるたび idInc 分だけ増える
              var mxid = maxID - idInc
              choose(
                langs.map { lang =>
                  mxid += idInc
                  new experimental.Transduction.ParikhTransduction(pst).preImage(lang, mxid)
                }
              ).iterator
            }
            for {
              rel <- acc
              choice <- {
                val lhs = rel.parikhAutomata.length - 1
                val automata = LazyList.from(rel.parikhAutomata(lhs))
                clauseChoices(automata, rel.maxID)
              }
            } yield {
              // 1. rel から最右要素を除く
              // 2. rel へ rhs に従って choice を追加する
              ParikhRelation.impose(
                rel.copy(parikhAutomata = rel.parikhAutomata.dropRight(1)),
                choice,
                rhs
              )
            }
        }
        .iterator
    }

    // 入力: (文字列変数インデックス，PST), (文字列変数インデックス, PAs), 整数制約
    // 出力: 逆像を計算していったときの conjunction の可能性を列挙するイテレータ
    def compileTriple(
        triple: Triple,
        logger: Logger
    )(alphabet: Set[Char]): Iterator[ParikhRelation[Int, Char, Int, String]] = {
      val Triple(assignments, assertions, arithFormulas) = triple
      require(
        assignments.map(_._1).sliding(2).forall(l => l.length < 2 || l(1) == l(0) + 1),
        "Not straight-line"
      )
      val initialConfig = organize(triple, alphabet)
      iteratePreImage(initialConfig)
      // val lastPSST = {
      //   val lastVarIdx = assignments.lastOption.map(_._1).getOrElse(assertions.map(_._1).max)
      //   val p = compileParikhAssertions(assertions, alphabet, lastVarIdx)
      //   val is = arithFormulas.flatMap(_.freeVars)
      //   val formulas = arithFormulas.map(_.renameVars[Either[String, Int]](Left.apply))
      //   p.copy(is = p.is ++ is, acceptFormulas = p.acceptFormulas ++ formulas)
      // }
      // val assignmentPSSTs = assignments.map(_._2(alphabet))
      // logger.trace("got the following PSSTs:")
      // (assignmentPSSTs :+ lastPSST).zipWithIndex.foreach {
      //   case (psst, i) => logger.trace(s"#$i: ${psst.sizes}")
      // }
      // (assignmentPSSTs :+ lastPSST).reduceLeft[SolverPSST[Char, String]] {
      //   case (p1, p2) =>
      //     logger.trace(s"compose ${p1.sizes} and ${p2.sizes}")
      //     p1 compose p2
      // }
    }

    // _1 : LazyList
    // _2 : index in relation → string variable name
    def compile(
        constraints: Seq[ParikhConstraint],
        additionalAlphabet: Set[Char],
        logger: Logger
        // ): (SolverPSST[Char, String], Map[Int, String]) = {
    ): (Iterator[SolverPR[Char, String]], Seq[String]) = {
      logger.trace("start compilation")
      val (varIdx, idxVar) = {
        val vi = stringVarIndex(constraints)
        (vi.toMap, vi.map(_._1))
      }
      val assignments = constraints.collect {
        case a: AtomicAssignment =>
          val rhs = a.dependeeVars.map(varIdx)
          (varIdx(a.lhsStringVar), a.toExpPST _, rhs)
      }
      val assertions = constraints.collect { case ParikhAssertion(sVar, lang)          => (varIdx(sVar), lang) }
      val arithFormula = constraints.collect { case IntConstraintIsParikhConstraint(f) => f }
      val alphabet = {
        val used = constraints.flatMap(_.usedAlphabet).toSet
        used ++ additionalAlphabet
      }
      val triple = Triple(assignments, assertions.groupMap(_._1)(_._2), arithFormula)
      val relGen = compileTriple(triple, logger)(alphabet)
      logger.trace(s"compilation done")
      (relGen, idxVar)
    }

  }
}
