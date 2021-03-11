package com.github.kmn4.sst.language

import com.github.kmn4.sst._
import com.github.kmn4.sst.math._
import com.github.kmn4.sst.math.Presburger.Sugar._
import com.github.kmn4.sst.machine._

import smtlib.theories.Ints.IntSort
import smtlib.theories.experimental.Strings.StringSort
import smtlib.theories.experimental.Strings
import smtlib.trees.Terms.{SNumeral, SString, Sort, Term => SMTTerm}

object Constraint {

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

  /** Unary transduction */
  trait Transduction[C] {
    def usedAlphabet: Set[C]

    /**
      * Construct NSST that performs this transduction and has non-empty set of variables.
      *
      * @param alphabet
      * @return NSST that performs this transduction and has non-empty set of variables.
      */
    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int]
  }

  case class ReplaceAll[C](target: Seq[C], word: Seq[C]) extends Transduction[C] {

    override def usedAlphabet: Set[C] = target.toSet ++ word.toSet

    /** Construct NSST which replaces `target` input string with `word` */
    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      type Q = Int
      type X = Int
      type UpdateX = Update[X, C]
      type Edges = Iterable[(Q, C, UpdateX, Q)]
      val x = 0
      val dfa = postfixDFA(target, alphabet)
      val states = dfa.states -- dfa.finalStates
      val edges: Edges = {
        // In each transition, DFA discards some prefix string (possibly empty one).
        // SST should store it in variable.
        for (q <- states; a <- alphabet)
          yield {
            val t = dfa.transition((q, a))
            val (r, append) =
              if (dfa.finalStates contains t) (dfa.q0, word)
              else {
                val qStored = target.take(q) ++ List(a)
                (t, qStored.take(qStored.length - t).toList)
              }
            val m = Map(x -> (Cop1(x) +: append.map[Cop[X, C]](Cop2.apply)).toList)
            (q, a, m, r)
          }
      }
      val outF: Map[Q, Set[Cupstar[X, C]]] = graphToMap {
        // On each state q, DFA has partially matched prefix of target string.
        states.toList.map(q => {
          val stored = target.take(q)
          q -> (List(Cop1(x)) ++ stored.toList.map(Cop2.apply))
        })
      }(identity)
      NSST[Q, C, C, X](states, alphabet, Set(x), edges.toSet, dfa.q0, outF)
    }

  }

  /** x(i) := replace_some x(j) target word */
  case class ReplaceSome[C](target: Seq[C], word: Seq[C]) extends Transduction[C] {

    override def usedAlphabet: Set[C] = target.toSet ++ word.toSet

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      type Q = Int
      type X = Int
      type UpdateX = Update[X, C]
      type Edges = Iterable[(Q, C, UpdateX, Q)]
      val x = 0
      val dfa = postfixDFA(target, alphabet)
      val states = dfa.states -- dfa.finalStates
      val edges: Edges = {
        // In each transition, DFA discards some prefix string (possibly empty one).
        // SST should store it in variable.
        states.flatMap { q =>
          alphabet.flatMap { a =>
            val t = dfa.transition((q, a))
            // Difference from ReplaceAll
            val (r, appends) =
              if (dfa.finalStates contains t) (dfa.q0, (Seq(word, target)))
              else {
                val qStored = target.take(q) ++ List(a)
                (t, Seq(qStored.take(qStored.length - t).toList))
              }
            appends.map(append => {
              val m = Map(x -> (Cop1(x) +: append.map[Cop[X, C]](Cop2.apply)).toList)
              (q, a, m, r)
            })
          }
        }
      }
      val outF: Map[Q, Set[Cupstar[X, C]]] = graphToMap {
        // On each state q, DFA has partially matched prefix of target string.
        states.toList.map(q => {
          val stored = target.take(q)
          q -> (List(Cop1(x)) ++ stored.toList.map(Cop2.apply))
        })
      }(identity)
      NSST[Q, C, C, X](states, alphabet, Set(x), edges.toSet, dfa.q0, outF)
    }
  }

  /** x(i) := insert(x(j), pos, word) */
  case class Insert[C](pos: Int, word: Seq[C]) extends Transduction[C] {

    override def usedAlphabet: Set[C] = word.toSet

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      type X = Int
      val x = 0
      type Q = Int
      type A = C
      type B = C
      type UpdateX = Update[X, B]
      type Edge = (Q, A, UpdateX, Q)
      val states = (0 to pos + 1).toSet
      val edges = states.flatMap { l =>
        if (l < pos) alphabet.map[Edge](a => (l, a, Map(x -> List(Cop1(x), Cop2(a))), l + 1))
        else if (l == pos)
          alphabet.map(a =>
            (l, a, Map(x -> (List(Cop1(x)) ++ word.map(c => Cop2(c)) ++ List(Cop2(a)))), l + 1)
          )
        else alphabet.map[Edge](a => (l, a, Map(x -> List(Cop1(x), Cop2(a))), l))
      }
      val outF = states
        .map(q =>
          q -> Set {
            if (q < pos) List(Cop1(x))
            else if (q == pos) List[Cop[X, B]](Cop1(x)) ++ word.map(c => Cop2(c))
            else List(Cop1(x))
          }
        )
        .toMap
      NSST(states, alphabet, Set(x), edges, 0, outF)
    }

  }

  /** x(i) := at(x(j), pos) */
  case class At[C](pos: Int) extends Transduction[C] {

    override def usedAlphabet: Set[C] = Set.empty

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = Substr(pos, 1).toSST(alphabet)
  }

  /** x(i) := reverse(x(j)) */
  case class Reverse[C]() extends Transduction[C] {

    override def usedAlphabet: Set[C] = Set.empty

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      NSST(
        Set(0),
        alphabet,
        Set(0),
        alphabet.map(a => (0, a, Map(0 -> List(Cop2(a), Cop1(0))), 0)),
        0,
        Map(0 -> Set(List(Cop1(0))))
      )
    }

  }

  /** x(i) := substr(x(j), from, len) */
  case class Substr[C](from: Int, len: Int) extends Transduction[C] {

    override def usedAlphabet: Set[C] = Set.empty

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      val x = 0
      val states = (0 to from + len).toSet
      val edges = states.flatMap { q =>
        if (q < from) alphabet.map(a => (q, a, Map(x -> Nil), q + 1))
        else if (q < from + len) alphabet.map(a => (q, a, Map(x -> List(Cop1(x), Cop2(a))), q + 1))
        else alphabet.map(a => (q, a, Map(x -> List(Cop1(x))), q))
      }
      val outF = states.map(q => q -> Set(List[Cop[Int, C]](Cop1(x))))
      NSST(states, alphabet, Set(x), edges.toSet, 0, outF.toMap)
    }
  }

  /** x(i) is prefix of x(j) */
  case class TakePrefix[C]() extends Transduction[C] {

    override def usedAlphabet: Set[C] = Set.empty

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      NSST(
        Set(0, 1),
        alphabet,
        Set(0),
        alphabet.flatMap(a =>
          Iterable(
            (0, a, Map(0 -> List(Cop1(0), Cop2(a))), 0),
            (0, a, Map(0 -> List(Cop1(0))), 1),
            (1, a, Map(0 -> List(Cop1(0))), 1)
          )
        ),
        0,
        Map(0 -> Set(List(Cop1(0))), 1 -> Set(List(Cop1(0))))
      )
    }

  }

  /** x(i) is suffix of x(j) */
  case class TakeSuffix[C]() extends Transduction[C] {

    override def usedAlphabet: Set[C] = Set.empty

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      NSST(
        Set(0, 1),
        alphabet,
        Set(0),
        alphabet.flatMap(a =>
          Iterable(
            (0, a, Map(0 -> List(Cop1(0))), 0),
            (0, a, Map(0 -> List(Cop1(0), Cop2(a))), 1),
            (1, a, Map(0 -> List(Cop1(0), Cop2(a))), 1)
          )
        ),
        0,
        Map(0 -> Set(List(Cop1(0))), 1 -> Set(List(Cop1(0))))
      )
    }
  }

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
        val dfa = Constraint.postfixDFA(target, alphabet)
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
        val dfa = Constraint.postfixDFA(target, alphabet)
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
  }

  trait ParikhTransduction[C, I] {
    def usedAlphabet: Set[C]
    def toParikhSST(alphabet: Set[C]): ParikhSST[Int, C, C, Int, Int, I]
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

  sealed trait ParikhConstraint[S] {
    def usedAlphabet: Set[Char]
    def dependerVars: Seq[S]
    def dependeeVars: Seq[S]
    // 文字列変数を付け替える
    def renameVars[T](f: S => T): ParikhConstraint[T]
  }
  sealed trait AtomicAssignment[S] extends ParikhConstraint[S] {
    def lhsStringVar: S

    override def dependerVars: Seq[S] = Seq(lhsStringVar)

    override def renameVars[T](f: S => T): AtomicAssignment[T]
  }
  case class ParikhAssignment[S](
      lhsStringVar: S,
      trans: ParikhTransduction[Char, String],
      rhsStringVar: S
  ) extends AtomicAssignment[S] {

    override def renameVars[T](f: S => T): AtomicAssignment[T] =
      copy(lhsStringVar = f(lhsStringVar), rhsStringVar = f(rhsStringVar))

    override def dependerVars: Seq[S] = Seq(lhsStringVar)

    override def dependeeVars: Seq[S] = Seq(rhsStringVar)

    override def usedAlphabet: Set[Char] = trans.usedAlphabet
  }
  // Left(word), Right(stringVar)
  case class CatAssignment[S](lhsStringVar: S, wordAndVars: Seq[Either[Seq[Char], S]])
      extends AtomicAssignment[S] {

    override def renameVars[T](f: S => T): AtomicAssignment[T] =
      copy(lhsStringVar = f(lhsStringVar), wordAndVars = wordAndVars.map(_.map(f)))

    override def dependerVars: Seq[S] = Seq(lhsStringVar)

    override def dependeeVars: Seq[S] = wordAndVars.flatMap(_.toOption)

    override def usedAlphabet: Set[Char] = wordAndVars.flatMap(_.left.getOrElse(Set.empty)).toSet
  }
  case class ParikhAssertion[S](stringVar: S, lang: ParikhLanguage[Char, String])
      extends ParikhConstraint[S] {

    override def dependerVars: Seq[S] = Seq.empty

    override def dependeeVars: Seq[S] = Seq(stringVar)

    override def usedAlphabet: Set[Char] = lang.usedAlphabet

    override def renameVars[T](f: S => T): ParikhAssertion[T] = copy(stringVar = f(stringVar))
  }
  type PureIntConstraint = Presburger.Formula[String]
  implicit class IntConstraintIsParikhConstraint[S](val formula: PureIntConstraint)
      extends ParikhConstraint[S] {

    override def dependerVars: Seq[S] = Seq.empty

    override def dependeeVars: Seq[S] = Seq.empty

    override def usedAlphabet: Set[Char] = Set.empty

    override def renameVars[T](f: S => T): IntConstraintIsParikhConstraint[T] =
      new IntConstraintIsParikhConstraint(formula)
  }
  object IntConstraintIsParikhConstraint {
    def unapply[S](c: ParikhConstraint[S]): Option[PureIntConstraint] = c match {
      case (c: IntConstraintIsParikhConstraint[S]) => Some(c.formula)
      case _                                       => None
    }
  }
}
