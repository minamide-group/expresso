// TODO rename this file
package com.github.kmn4.sst

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

  class Checker(psst: SolverPSST[Char, String], idxVar: Map[Int, String]) {
    // _1: Int var -> value, _2: Log var -> value
    def witnessVector: () => Option[(Map[String, Int], Map[Int, Int])] =
      Cacher { psst.ilVectorOption }.getOrCalc _
    // _1: Str var -> value, _2: Int var -> value
    val models: () => Option[(Map[String, String], Map[String, Int])] = Cacher {
      witnessVector().map {
        case (iv, lv) =>
          val (_, output) = psst.inputOutputFor(lv)
          (parseStrModel(output), parseIntModel(iv))
      }
    }.getOrCalc _
    def parseStrModel(output: Seq[Option[Char]]): Map[String, String] = {
      var buf = output
      var idx = 0
      var res = Map.empty[String, Seq[Char]]
      while (buf.nonEmpty) {
        val took = buf.takeWhile(_.nonEmpty).flatten
        buf = buf.drop(took.length + 1)
        res += (idxVar(idx) -> took)
        idx += 1
      }
      res.view.mapValues(_.mkString).toMap
    }
    def parseIntModel(iv: Map[String, Int]): Map[String, Int] =
      iv.collect { case (name, value) if name.indexOf("user_") == 0 => name.drop(5) -> value }
    def checkSat(): Boolean = witnessVector().nonEmpty
    def getModel(): Option[(Map[String, String], Map[String, Int])] = models()
  }

  val (checker, resetChecker) = {
    val c = Cacher[Checker] {
      val (psst, idxVar) = Compiler.compile(constraints, alphabet, logger)
      new Checker(psst, idxVar)
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
    def toSolverPSST(varIdx: Map[String, Int])(alphabet: Set[Char]): SolverPSST[Char, String]
  }
  case class ParikhAssignment(
      lhsStringVar: String,
      trans: ParikhTransduction[Char, String],
      rhsStringVar: String
  ) extends AtomicAssignment {

    override def dependerVars: Seq[String] = Seq(lhsStringVar)

    override def dependeeVars: Seq[String] = Seq(rhsStringVar)

    def usedAlphabet: Set[Char] = trans.usedAlphabet
    def toSolverPSST(varIdx: Map[String, Int])(alphabet: Set[Char]): SolverPSST[Char, String] =
      trans.toSolverPSST(alphabet, varIdx(lhsStringVar), varIdx(rhsStringVar))
  }
  // Left(word), Right(stringVar)
  case class CatAssignment(lhsStringVar: String, wordAndVars: Seq[Either[Seq[Char], String]])
      extends AtomicAssignment {

    override def dependerVars: Seq[String] = Seq(lhsStringVar)

    override def dependeeVars: Seq[String] = wordAndVars.flatMap(_.toOption)

    def usedAlphabet: Set[Char] = wordAndVars.flatMap(_.left.toOption.map(_.toSet).getOrElse(Set.empty)).toSet
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
    def stringVarIndex(constraints: Seq[ParikhConstraint]): Map[String, Int] = {
      val dependers = constraints.flatMap(_.dependerVars).distinct
      val dependees = constraints.flatMap(_.dependeeVars).distinct
      val independents = dependees.diff(dependers)
      (independents ++ dependers).distinct.zipWithIndex.toMap
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

    def compileTriple(
        assignments: Seq[
          (Int, Set[Char] => SolverPSST[Char, String])
        ], // ([lhsVarIdx], [corresponding solver PSST])
        assertions: Map[Int, Seq[ParikhLanguage[Char, String]]], // [string var idx] in [Parikh langs]
        arithFormulas: Seq[PureIntConstraint], // formula over int variables
        logger: Logger
    )(alphabet: Set[Char]): SolverPSST[Char, String] = {
      require(
        assignments.map(_._1).sliding(2).forall(l => l.length < 2 || l(1) == l(0) + 1),
        "Not straight-line"
      )
      val lastPSST = {
        val lastVarIdx = assignments.lastOption.map(_._1).getOrElse(assertions.map(_._1).max)
        val p = compileParikhAssertions(assertions, alphabet, lastVarIdx)
        val is = arithFormulas.flatMap(_.freeVars)
        val formulas = arithFormulas.map(_.renameVars[Either[String, Int]](Left.apply))
        p.copy(is = p.is ++ is, acceptFormulas = p.acceptFormulas ++ formulas)
      }
      val assignmentPSSTs = assignments.map(_._2(alphabet))
      logger.trace("got the following PSSTs:")
      (assignmentPSSTs :+ lastPSST).zipWithIndex.foreach {
        case (psst, i) => logger.trace(s"#$i: ${psst.sizes}")
      }
      (assignmentPSSTs :+ lastPSST).reduce[SolverPSST[Char, String]] {
        case (p1, p2) =>
          logger.trace(s"compose ${p1.sizes} and ${p2.sizes}")
          p1 compose p2
      }
    }

    // _2: Index of string in PSST output -> String var name
    def compile(
        constraints: Seq[ParikhConstraint],
        additionalAlphabet: Set[Char],
        logger: Logger
    ): (SolverPSST[Char, String], Map[Int, String]) = {
      logger.trace("start compilation")
      val varIdx = stringVarIndex(constraints)
      val assignments = constraints.collect {
        case a @ ParikhAssignment(lhs, trans, rhs) => (varIdx(lhs), a.toSolverPSST(varIdx) _)
        case a @ CatAssignment(lhs, wordAndVars)   => (varIdx(lhs), a.toSolverPSST(varIdx) _)
      }
      val assertions = constraints.collect { case ParikhAssertion(sVar, lang)          => (varIdx(sVar), lang) }
      val arithFormula = constraints.collect { case IntConstraintIsParikhConstraint(f) => f }
      val alphabet = {
        val used = constraints.flatMap(_.usedAlphabet).toSet
        used ++ additionalAlphabet
      }
      val psst = compileTriple(assignments, assertions.groupMap(_._1)(_._2), arithFormula, logger)(alphabet)
      logger.trace(s"composition done, got PSST ${psst.sizes}")
      (psst, varIdx.map { case (x, i) => i -> x })
    }

  }
}
