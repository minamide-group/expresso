package com.github.kmn4.sst

import smtlib.theories.experimental.Strings
import smtlib.trees.Commands._
import smtlib.trees.Terms
import smtlib.trees.Terms._

import Constraint._
import Solver._

object Solver {
  object SimpleQualID {
    def apply(name: String): QualifiedIdentifier = QualifiedIdentifier(SimpleIdentifier(SSymbol(name)), None)
    def unapply(term: Term): Option[String] = term match {
      case QualifiedIdentifier(SimpleIdentifier(SSymbol(name)), None) => Some(name)
      case _                                                          => None
    }
  }
  object SimpleApp {
    def apply(name: String, args: Term*): Term = FunctionApplication(SimpleQualID(name), args)
    def unapply(term: Term): Option[(String, Seq[Term])] = term match {
      case FunctionApplication(SimpleQualID(name), terms) => Some((name, terms))
      case _                                              => None
    }
  }

  def expectRegExp(t: Term): RegExp[Char] =
    t match {
      case Strings.ToRegex(SString(s)) =>
        if (s.nonEmpty)
          s.map[RegExp[Char]](CharExp.apply).reduce[RegExp[Char]] { case (e1, e2) => CatExp(e1, e2) }
        else EpsExp
      case Strings.Regex.*(t) => StarExp(expectRegExp(t))
      case Strings.Regex.+(t) =>
        val re = expectRegExp(t)
        CatExp(re, StarExp(re))
      case Strings.Regex.Concat(ts @ _*) =>
        ts.tail.foldLeft(expectRegExp(ts.head)) { case (acc, t) => CatExp(acc, expectRegExp(t)) }
      case Strings.Regex.Union(ts @ _*) =>
        ts.tail.foldLeft(expectRegExp(ts.head)) { case (acc, t) => OrExp(acc, expectRegExp(t)) }
      case Strings.Regex.Range(SString(c1), SString(c2)) if c1.length == 1 && c2.length == 1 =>
        throw new NotImplementedError("re.range is not implemented")
      case SimpleApp("re.comp", Seq(e)) => CompExp(expectRegExp(e))
      case Strings.Regex.AllChar()      => DotExp
      case SimpleQualID("re.all")       => StarExp(DotExp)
      case _                            => throw new Exception(s"Cannot interpret given S-expression as regular expression: $t")
    }

  type SolverOption = Unit

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
    val outF: Map[Q, Set[Cupstar[X, B]]] = Map((n, 0) -> Set(output))
    val updates = updateMonoid(xs)
    type Edges = Set[(Q, A, Update[X, B], Q)]
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

  type SolverSST[A] = NSST[Int, Option[A], Option[A], Int]

  def expectPCRE(t: Term): Replacer.PCRE[Char, Int] = {
    type RE = Replacer.PCRE[Char, Int]
    var group = 0
    def nextGroup(): Int = {
      group += 1
      group
    }
    def aux(t: Term): RE = t match {
      case SimpleApp("str.to_pcre", Seq(SString(w))) =>
        w.map[RE](c => Replacer.PCRE.Chars(Set(c)))
          .fold[Replacer.PCRE[Char, Int]](Replacer.PCRE.Eps())(Replacer.PCRE.Cat.apply)
      case SimpleApp("pcre.alt", ts)   => ts.map(aux).reduce[RE](Replacer.PCRE.Alt.apply)
      case SimpleApp("pcre.++", ts)    => ts.map(aux).reduce[RE](Replacer.PCRE.Cat.apply)
      case SimpleApp("pcre.*", Seq(t)) => Replacer.PCRE.Greedy(aux(t))
      case SimpleApp("pcre.+", Seq(t)) =>
        val pcre = aux(t)
        Replacer.PCRE.Cat(pcre, Replacer.PCRE.Greedy(pcre))
      case SimpleApp("pcre.*?", Seq(t)) => Replacer.PCRE.NonGreedy(aux(t))
      case SimpleApp("pcre.group", Seq(t)) =>
        val group = nextGroup()
        Replacer.PCRE.Group(aux(t), group)
      case SimpleQualID("pcre.allchar") => Replacer.PCRE.AllChar()
      case _                            => throw new Exception(s"${t.getPos}: PCRE expected but found: $t")
    }
    aux(t)
  }

  def expectReplacement(t: Term): Replacer.Replacement[Char, Int] = t match {
    case SimpleApp("pcre.replacement", ts) =>
      Replacer.Replacement(
        ts.flatMap {
          case SString(w)            => w.map(Left.apply)
          case SNumeral(i) if i == 0 => Seq(Right(None))
          case SNumeral(i) if i > 0  => Seq(Right(Some(i.toInt)))
          case t                     => throw new Exception(s"${t.getPos}: PCRE Replacement component expected but found: $t")
        }
      )
    case _ => throw new Exception(s"${t.getPos}: PCRE Replacement expected but found: $t")
  }

  object SimpleTransduction {
    // (rhs, transduction)
    def unapply(e: Term): Option[(String, Transduction[Char])] =
      e match {
        case SimpleApp("str.replaceall", Seq(SimpleQualID(name), SString(target), SString(word))) =>
          Some((name, ReplaceAll(target, word)))
        case SimpleApp("str.replace_all", Seq(SimpleQualID(name), SString(target), SString(word))) =>
          Some((name, ReplaceAll(target, word)))
        case SimpleApp("str.replace_some", Seq(SimpleQualID(name), SString(target), SString(word))) =>
          Some((name, ReplaceSome(target, word)))
        case Strings.At(SimpleQualID(name), SimpleQualID(pos)) =>
          Some((name, At(pos.toInt)))
        case SimpleApp("str.replace_pcre", Seq(SimpleQualID(name), pcre, replacement)) =>
          Some((name, Replacer.ReplacePCRE(expectPCRE(pcre), expectReplacement(replacement))))
        case SimpleApp("str.replace_pcre_all", Seq(SimpleQualID(name), pcre, replacement)) =>
          Some((name, Replacer.ReplacePCREAll(expectPCRE(pcre), expectReplacement(replacement))))
        case SimpleApp("str.insert", Seq(SimpleQualID(name), SNumeral(pos), SString(word))) =>
          Some((name, Insert(pos.toInt, word)))
        case SimpleApp("str.reverse", Seq(SimpleQualID(name))) =>
          Some((name, Reverse()))
        case Strings.Substring(SimpleQualID(name), SNumeral(from), SNumeral(len)) =>
          Some((name, Substr(from.toInt, len.toInt)))
        case _ => None
      }
  }
}
