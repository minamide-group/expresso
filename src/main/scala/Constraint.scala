package com.github.kmn4.sst

import smtlib.theories.Ints.IntSort
import smtlib.theories.experimental.Strings.StringSort
import smtlib.trees.Terms.Sort
import Solver._

object Constraint {

  /** Integer-parameterized transduction. */
  trait ParameterizedTransduction[C] {

    /** A SST whose output is a pair of strings delimited by '#' (which is represented by `None`). */
    def toPairValuedSST(alphabet: Set[C]): NSST[Int, C, Option[C], Int]

    def outputStringNum: Int

    def defineStringNum: Int

    /**
      * The number of integer variables constrained by this transduction.
      * For example, taking substring uses two parameters (say i and l), i for the index of the head and
      * l for the length to take. In order to let parameters range over arbitrary integers,
      * y := substr x i l CONSTRAINS i and l by adding some formula to the set of integer constraints.
      * See substr implementation for details.
      */
    def intVarNum: Int

    /**
      * Presburger formulas that constrain ingeter variables by defining
      * their relation with length of the input / outputs of the SST.
      * A variable `Left(i)` should mean the i-th integer variable, whereas `Right(0)`
      * mean the input SST reads and `Right(i)` with i > 0 is the i-th output string.
      *
      * The sequence of formulas is interpreted as conjunction.
      */
    def relationFormula: Seq[Presburger.Formula[Either[Int, Int]]]

    /**
      * Returns NSST that reads a '#' demilited input and ouputs '#' delimited strings.
      *
      * @param i The SST will read `i - 1` strings and output `i - 1 + outputStringNum` strings.
      * @param j The index of string which the SST will transduce.
      */
    def toSolverSST(i: Int, j: Int, alphabet: Set[C]): SolverSST[C] = {
      sealed trait X
      case object XIn extends X
      case class XJ(x: Int) extends X
      type Q = (Int, Int)
      type A = Option[C]
      type UpdateX = Update[X, A]
      type Edges = Iterable[(Q, A, UpdateX, Q)]
      val jsst = this.toPairValuedSST(alphabet)
      val xjs: Set[X] = jsst.variables.map(XJ.apply)
      val xj = xjs.head
      val base = solverNsstTemplate[C, X](i, alphabet, XIn, xjs, List(Cop1(XIn), Cop1(xj), Cop2(None)))
      val xs = base.variables
      val updates: Monoid[UpdateX] = updateMonoid(xs)
      val states: Set[Q] = base.states - ((j, 0)) ++ jsst.states.map((j, _))
      val edges: Edges = {
        val baseNoJ = base.edges.filter { case (q, a, m, r) => (q._1 != j) && (r._1 != j) }
        def unit(a: A): UpdateX = updates.unit + (XIn -> List(Cop1(XIn), Cop2(a)))
        def reset(a: A): UpdateX = xs.map(_ -> Nil).toMap + (XIn -> List(Cop1(XIn), Cop2(a)))
        val toJ = ((j - 1, 0), None, unit(None), (j, jsst.q0))
        def embedList(l: Cupstar[Int, A]): Cupstar[X, A] = l.map(_.map1(XJ.apply))
        def embedUpdate(m: Update[Int, A]): Update[X, A] =
          m.map { case (x, l) => XJ(x) -> embedList(l) }
        val withinJ: Edges = jsst.edges.map {
          case (q, a, m, r) =>
            (((j, q), Some(a), embedUpdate(m) + (XIn -> List(Cop1(XIn), Cop2(Some(a)))), (j, r)))
        }
        val fromJ: Edges =
          for ((qf, s) <- jsst.outF; l <- s)
            yield ((j, qf), None, reset(None) + (xj -> embedList(l)), (j + 1, 0))

        baseNoJ + toJ ++ withinJ ++ fromJ
      }
      for (e @ (_, _, m, _) <- edges if !NSST.isCopylessUpdate(m)) println(e)
      base
        .copy(
          states = states,
          variables = xs ++ xjs,
          edges = edges.toSet,
          q0 = if (j == 0) (j, jsst.q0) else (0, 0)
        )
        .renamed
    }
  }

  /**
    * For (assert (= j (str.indexof x w 0))), where w is a NON-EMPTY constant string and j a integer variable.
    *
    * @param target
    */
  case class IndexOfFromZero[C](target: Seq[C]) extends ParameterizedTransduction[C] {
    def outputStringNum: Int = 1
    def defineStringNum: Int = 0
    def intVarNum: Int = 1
    def toPairValuedSST(alphabet: Set[C]): NSST[Int, C, Option[C], Int] =
      UntilFirst(target).toPairValuedSST(alphabet)
    def relationFormula: Seq[Presburger.Formula[Either[Int, Int]]] = {
      import Presburger._
      type T = Term[Either[Int, Int]]
      val j: T = Var(Left(0))
      val d: T = Var(Right(0))
      val r: T = Var(Right(1))
      Seq(
        Implies(Ge(r, d), Eq(j, Const(-1))),
        Implies(Lt(r, d), Eq(j, r))
      )
    }
  }

  object IndexOfFromZero {
    def apply[C](target: Seq[C]): IndexOfFromZero[C] = {
      require(target.nonEmpty)
      new IndexOfFromZero(target)
    }
  }

  /** For (assert (= y (str.substr x i l))), where both i and l are variables. */
  case class GeneralSubstr[C]() extends ParameterizedTransduction[C] {

    def toPairValuedSST(alphabet: Set[C]): NSST[Int, C, Option[C], Int] = {
      val xs = Set(0, 1)
      val unit: Update[Int, Option[C]] = updateMonoid(xs).unit
      val edges = alphabet.flatMap { a =>
        Iterable(
          (0, a, unit + (1 -> List(Cop1(1), Cop2(Some(a)))), 0),
          (0, a, unit + (0 -> List(Cop1(0), Cop2(Some(a)))), 1),
          (1, a, unit + (0 -> List(Cop1(0), Cop2(Some(a)))), 1),
          (1, a, unit, 2),
          (2, a, unit, 2)
        )
      }
      NSST(
        Set(0, 1, 2),
        alphabet,
        xs,
        edges,
        0,
        (0 to 2).map(_ -> Set(List[Cop[Int, Option[C]]](Cop1(0), Cop2(None), Cop1(1)))).toMap
      )
    }

    def outputStringNum: Int = 2
    // How many string variables will be in the LHS of this transduction.
    def defineStringNum: Int = 1
    // How many int variables does this transduction need / constrain ?
    def intVarNum: Int = 2
    def relationFormula: Seq[Presburger.Formula[Either[Int, Int]]] = {
      // y := substr x i l
      // r0, r1 := T(d)
      // r0 will be y, whereas r1 is temporary
      // What relation holds between |d|, |r0|, |r1|, i and l ?
      // i < 0 || i >= len(d) || l < 0 => len(r0) == 0
      // 0 <= i && i < len(d) && 0 <= l && l <= len(d) - i => len(r1) == i && len(r0) == l
      // 0 <= i && i < len(d) && l > len(d) - i => len(r1) == i && len(r0) == len(d) - i
      import Presburger._
      type T = Term[Either[Int, Int]]
      val i: T = Var(Left(0))
      val l: T = Var(Left(1))
      val d: T = Var(Right(0))
      val r0: T = Var(Right(1))
      val r1: T = Var(Right(2))
      val zero: T = Const(0)
      val idxOutOrNegLen = Disj(Seq(Lt(i, zero), Ge(i, d), Le(l, zero)))
      Seq(
        Implies(idxOutOrNegLen, Eq(r0, zero)),
        Implies(Conj(Seq(Not(idxOutOrNegLen), Le(l, Sub(d, i)))), Conj(Seq(Eq(r1, i), Eq(r0, l)))),
        Implies(Conj(Seq(Not(idxOutOrNegLen), Gt(l, Sub(d, i)))), Conj(Seq(Eq(r1, i), Eq(r0, Sub(d, i)))))
      )
    }
  }

  /** Unary transduction */
  trait Transduction[C] extends ParameterizedTransduction[C] {
    def intVarNum: Int = 0
    def relationFormula: Seq[Presburger.Formula[Either[Int, Int]]] = Nil
    def outputStringNum: Int = 1
    def defineStringNum: Int = 1
    def toPairValuedSST(alphabet: Set[C]): NSST[Int, C, Option[C], Int] = {
      def embedList(l: Cupstar[Int, C]): Cupstar[Int, Option[C]] = l.map(_.map2(Some.apply))
      def embedUpdate(m: Update[Int, C]): Update[Int, Option[C]] =
        m.map { case (x, l) => x -> embedList(l) }
      val s = toSST(alphabet)
      s.copy(
        edges = s.edges.map { case (q, c, m, r) => (q, c, embedUpdate(m), r) },
        partialF = s.partialF.map { case (q, s) => q -> s.map(embedList) }
      )
    }

    /**
      * Construct NSST that performs this transduction and has non-empty set of variables.
      *
      * @param alphabet
      * @return NSST that performs this transduction and has non-empty set of variables.
      */
    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int]
  }

  case class ReplaceAll[C](target: Seq[C], word: Seq[C]) extends Transduction[C] {

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
      val outF: Map[Q, Set[Cupstar[X, C]]] = NSST.graphToMap {
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
      val outF: Map[Q, Set[Cupstar[X, C]]] = NSST.graphToMap {
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
    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = Substr(pos, 1).toSST(alphabet)
  }

  /** x(i) := reverse(x(j)) */
  case class Reverse[C]() extends Transduction[C] {

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

  /** x(i) := prefix of x(j) that excludes longet prefix of x(j) that excludes leftmost `target`.
    * If x(j) does not contain `target`, then x(i) will be x(j). */
  case class UntilFirst[C](target: Seq[C]) extends Transduction[C] {

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      type Q = Int
      type X = Int
      type UpdateX = Update[X, C]
      type Edges = Iterable[(Q, C, UpdateX, Q)]
      val x = 0
      val dfa = postfixDFA(target, alphabet)
      val states = dfa.states
      val edges: Edges = {
        for (q <- states; a <- alphabet)
          yield
            if (!dfa.finalStates(q)) {
              val r = dfa.transition((q, a))
              val append =
                if (dfa.finalStates(r)) Seq.empty
                else {
                  val stored = target.take(q) ++ List(a)
                  stored.take(stored.length - r)
                }
              val m = Map(x -> (Cop1(x) :: append.map(Cop2.apply).toList))
              (q, a, m, r)
            } else {
              (q, a, Map(x -> List[Cop[Int, C]](Cop1(x))), q)
            }
      }
      val outF: Map[Q, Set[Cupstar[X, C]]] =
        // On each state q, DFA has partially matched prefix of target string.
        states
          .map(q =>
            q -> {
              // On non-final states q, it should append to variable the prefix of target string stored in DFA.
              if (!dfa.finalStates(q)) {
                val stored = target.take(q)
                Set(List[Cop[X, C]](Cop1(x)) ++ stored.toList.map(Cop2.apply))
              } else {
                // On the other hand, being on final states means target has been found.
                // Thus it should output variable as is.
                Set(List[Cop[X, C]](Cop1(x)))
              }
            }
          )
          .toMap
      NSST[Q, C, C, X](states, alphabet, Set(x), edges.toSet, dfa.q0, outF)
    }
  }

  sealed trait Var
  case class StringVar(name: String) extends Var
  case class IntVar(name: String) extends Var

  sealed trait AtomicConstraint[A]
  case class Constant[A](lhs: StringVar, word: Seq[A]) extends AtomicConstraint[A]
  case class CatCstr[A](lhs: StringVar, rhs: Seq[Either[Seq[A], StringVar]]) extends AtomicConstraint[A]
  case class AtomicAssignment[A](lhs: Seq[StringVar], trans: ParameterizedTransduction[A], rhs: StringVar)
      extends AtomicConstraint[A]
  trait TransductionConstraint[A] {
    def trans: ParameterizedTransduction[A]
    def readingVar: StringVar
    def definedVars: Seq[StringVar]
    def intVars: Seq[IntVar]
    def atomicAssignAndIntConstraint(unused: Iterator[Int]): (AtomicAssignment[A], Seq[IntConstraint]) = {
      val fs = trans.relationFormula
      val tempVars =
        unused
          .take(trans.outputStringNum - trans.defineStringNum)
          .map(i => StringVar(s".s$i"))
          .toSeq
      val stringVars = readingVar +: (definedVars ++ tempVars)
      (
        AtomicAssignment(definedVars ++ tempVars, trans, readingVar),
        fs.map(f =>
          Presburger.Formula.renameVars(f) {
            case Left(i)  => intVars(i)
            case Right(i) => stringVars(i)
          }
        )
      )
    }
  }
  case class SimpleTransCstr[A](lhs: StringVar, trans: Transduction[A], rhs: StringVar)
      extends TransductionConstraint[A] {
    def readingVar: StringVar = rhs
    def definedVars: Seq[StringVar] = Seq(lhs)
    def intVars: Seq[IntVar] = Nil
  }
  case class ParamTransCstr[A](
      trans: ParameterizedTransduction[A],
      readingVar: StringVar,
      definedVars: Seq[StringVar],
      intVars: Seq[IntVar]
  ) extends TransductionConstraint[A]

  /** Interpret terms made from StringVar as length of them. */
  type IntConstraint = Presburger.Formula[Var]
  type IntExp = Presburger.Term[Var]

  case class RegexConstraint[A](v: StringVar, re: RegExp[A])
  case class SLConstraint[A](
      as: Seq[AtomicConstraint[A]],
      is: Seq[IntConstraint],
      rs: Seq[RegexConstraint[A]]
  )
  object SLConstraint {
    def empty[A]: SLConstraint[A] = SLConstraint(Seq.empty, Seq.empty, Seq.empty)
  }

}

object ConstraintExamples {
  import Constraint._
  // Zhu's case 1
  val c1 = {
    val Seq(x0, x1, x2) = (0 to 2).map(i => StringVar(s"x$i"))
    val mock = LazyList.from(0).iterator
    val (s1, _) = SimpleTransCstr(x1, ReplaceAll("a", "b"), x0).atomicAssignAndIntConstraint(mock)
    val s2 = CatCstr(x2, List(Left("a".toList), Right(x1), Left("b".toList)))
    val r = RegexConstraint(x2, CatExp(CatExp(CharExp('a'), StarExp(CharExp('b'))), CharExp('a')))
    SLConstraint(Seq(s1, s2), Nil, Seq(r))
  }
  // Zhu's case 2
  val c2 = {
    val Seq(x0, x1, x2, x3, x4) = (0 to 4).map(i => StringVar(s"x$i"))
    val mock = LazyList.from(0).iterator
    val (s1, _) = SimpleTransCstr(x2, ReplaceAll("<sc>", "a"), x0).atomicAssignAndIntConstraint(mock)
    val (s2, _) = SimpleTransCstr(x3, ReplaceAll("<sc>", "a"), x1).atomicAssignAndIntConstraint(mock)
    val s3 = CatCstr[Char](x4, List(Right(x2), Right(x3)))
    val r = RegexConstraint(x4, "a<sc>a".toSeq.map(CharExp.apply).reduce[RegExp[Char]] {
      case (e1, e2) => CatExp(e1, e2)
    })
    SLConstraint(Seq(s1, s2, s3), Nil, Seq(r))
  }
  // Involving integer constraint
  val c3 = {
    import Presburger._
    val Seq(x0, x1, x2) = (0 to 2).map(i => StringVar(s"x$i"))
    val mock = LazyList.from(0).iterator
    val (s1, _) = SimpleTransCstr(x1, ReplaceAll("ab", "c"), x0).atomicAssignAndIntConstraint(mock)
    val (s2, _) = SimpleTransCstr(x2, ReplaceAll("ac", "aaaa"), x1).atomicAssignAndIntConstraint(mock)
    val i1: Formula[Constraint.Var] = Lt(Var(x0), Const(5)) // x0 <= 4
    val i2: Formula[Constraint.Var] = Lt(Add(Seq(Var(x0), Const(1))), Var(x2)) // x0 + 2 <= x2
    SLConstraint(Seq(s1, s2), Seq(i1, i2), Nil)
  }
  val c4 = {
    import Presburger._
    val x = StringVar("x")
    val y = StringVar("y")
    val i = IntVar("i")
    val j = IntVar("j")
    val k = IntVar("k")
    val unused = LazyList.from(0).iterator
    val (s1, is1) =
      ParamTransCstr(IndexOfFromZero("ab"), x, Seq.empty, Seq(j)).atomicAssignAndIntConstraint(unused)
    val (s2, is2) =
      ParamTransCstr(GeneralSubstr[Char](), x, Seq(y), Seq(i, k)).atomicAssignAndIntConstraint(unused)
    val i1: IntConstraint = Eq(Var(i), Const(0))
    val i2: IntConstraint = Eq(Var(k), Const(2))
    val r = RegexConstraint(y, CompExp(CatExp(CharExp('a'), CharExp('b'))))
    SLConstraint(Seq(s1, s2), Seq(i1, i2) ++ is1 ++ is2, Seq(r))
  }
}
