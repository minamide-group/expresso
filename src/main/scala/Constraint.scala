package com.github.kmn4.sst

// Input .smt2 file must declare string variables in straight-line order,
// and must not declare unused string variables.
object Constraint {
  import Solver._

  /** Unary transduction */
  sealed trait Transduction[C] {

    /**
      * Construct SST that represents x(i) := T(x(j)).
      *
      * @param i
      * @param j
      * @param alphabet
      * @return
      */
    def toSolverSST(i: Int, j: Int, alphabet: Set[C]): Solver.SolverSST[C]
  }

  case class ReplaceAll[C](target: Seq[C], word: Seq[C]) extends Transduction[C] {

    /** Construct NSST which replaces `target` in `j`-th input string with `word`,
      * and output it as `i`-th string. */
    def toSolverSST(i: Int, j: Int, alphabet: Set[C]): Solver.SolverSST[C] = {
      type Q = (Int, Int)
      sealed trait X
      case object XIn extends X
      case object XJ extends X
      type A = Option[C]
      type B = Option[C]
      type Update = Concepts.Update[X, B]
      val base = solverNsstTemplate[C, X](i, alphabet, XIn, Set(XJ), List(Cop1(XIn), Cop1(XJ), Cop2(None)))
      val xs = base.variables
      val updates: Monoid[Update] = Concepts.updateMonoid(xs)
      val dfa = postfixDFA(target, alphabet)
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
            for (q <- states; a <- alphabet)
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
      NSST[Q, A, B, X](
        states,
        alphabet.map(Some(_): Option[C]) + None,
        xs,
        edges,
        q0,
        base.partialF
      ).renamed
    }
  }

  /** x(i) := insert(x(j), pos, word) */
  case class Insert[C](pos: Int, word: Seq[C]) extends Transduction[C] {

    def toSolverSST(i: Int, j: Int, alphabet: Set[C]): Solver.SolverSST[C] = {
      sealed trait X
      case object XIn extends X
      case object XJ extends X
      type Q = (Int, Int)
      type A = Option[C]
      type B = Option[C]
      type Update = Concepts.Update[X, B]
      type Edge = (Q, A, Update, Q)
      val base = solverNsstTemplate[C, X](i, alphabet, XIn, Set(XJ), List(Cop1(XIn), Cop1(XJ), Cop2(None)))
      val newStates = (0 to pos + 1).map((j, _)).toSet
      val baseEdges = base.edges.view.filterNot { case (q, _, _, _) => q._1 == j }
      val newEdges = newStates.view.flatMap {
        case (_, l) if l < pos =>
          alphabet.map[Edge](a =>
            (
              (j, l),
              Some(a),
              Map(XIn -> List(Cop1(XIn), Cop2(Some(a))), XJ -> List(Cop1(XJ), Cop2(Some(a)))),
              (j, l + 1)
            )
          ) + (((j, l), None, Map(XIn -> List(Cop1(XIn), Cop2(None)), XJ -> List(Cop1(XJ))), (j + 1, 0)))
        case (_, l) if l == pos =>
          base.in.map[Edge](a =>
            (
              (j, l),
              a,
              Map(
                XIn -> List(Cop1(XIn), Cop2(a)),
                XJ -> (List(Cop1(XJ)) ++ word.map(c => Cop2(Some(c))) ++ List(Cop2(a)))
              ),
              (j, l + 1)
            )
          ) + (
            (
              (j, l),
              None,
              Map(
                XIn -> List(Cop1(XIn), Cop2(None)),
                XJ -> (List(Cop1(XJ)) ++ word.map(c => Cop2(Some(c))))
              ),
              (j + 1, 0)
            )
          )
        case (_, l) if l == pos + 1 =>
          alphabet.map[Edge](a =>
            (
              (j, l),
              Some(a),
              Map(XIn -> List(Cop1(XIn), Cop2(Some(a))), XJ -> List(Cop1(XJ), Cop2(Some(a)))),
              (j, l)
            )
          ) + (((j, l), None, Map(XIn -> List(Cop1(XIn), Cop2(None)), XJ -> List(Cop1(XJ))), (j + 1, 0)))
      }
      base
        .copy(
          states = base.states ++ newStates,
          edges = (baseEdges ++ newEdges).toSet
        )
        .renamed

    }

  }

  /** x(i) := at(x(j), pos) */
  case class At[C](pos: Int) extends Transduction[C] {

    def toSolverSST(i: Int, j: Int, alphabet: Set[C]): Solver.SolverSST[C] =
      Substr(pos, 1).toSolverSST(i, j, alphabet)

  }

  /** x(i) := reverse(x(j)) */
  case class Reverse[C]() extends Transduction[C] {

    def toSolverSST(i: Int, j: Int, alphabet: Set[C]): Solver.SolverSST[C] = {
      sealed trait X
      case object XIn extends X
      case object XJ extends X
      val base = solverNsstTemplate[C, X](i, alphabet, XIn, Set(XJ), List(Cop1(XIn), Cop1(XJ), Cop2(None)))
      val edges = base.edges.map {
        case (q, a, m, r) if q._1 == j && a != None => (q, a, m + (XJ -> List(Cop2(a), Cop1(XJ))), r)
        case edge                                   => edge
      }
      base.copy(edges = edges).renamed
    }

  }

  /** x(i) := substr(x(j), from, len) */
  case class Substr[C](from: Int, len: Int) extends Transduction[C] {

    def toSolverSST(i: Int, j: Int, alphabet: Set[C]): Solver.SolverSST[C] = {
      sealed trait X
      case object XIn extends X
      case object XJ extends X
      type Q = (Int, Int)
      type A = Option[C]
      type B = Option[C]
      type Update = Concepts.Update[X, B]
      type Edge = (Q, A, Update, Q)
      val base = solverNsstTemplate[C, X](i, alphabet, XIn, Set(XJ), List(Cop1(XIn), Cop1(XJ), Cop2(None)))
      val newStates = (0 to from + len).map((j, _)).toSet
      val baseEdges = base.edges.view.filterNot { case (q, _, _, _) => q._1 == j }
      val newEdges = newStates.view.flatMap {
        case (_, l) if l < from =>
          alphabet.map[Edge](a =>
            ((j, l), Some(a), Map(XIn -> List(Cop1(XIn), Cop2(Some(a))), XJ -> Nil), (j, l + 1))
          ) + (((j, l), None, Map(XIn -> List(Cop1(XIn), Cop2(None)), XJ -> List(Cop1(XJ))), (j + 1, 0)))
        case (_, l) if l < from + len =>
          base.in.map[Edge](a =>
            ((j, l), a, Map(XIn -> List(Cop1(XIn), Cop2(a)), XJ -> (List(Cop1(XJ), Cop2(a)))), (j, l + 1))
          ) + (((j, l), None, Map(XIn -> List(Cop1(XIn), Cop2(None)), XJ -> List(Cop1(XJ))), (j + 1, 0)))
        case (_, l) =>
          alphabet.map[Edge](a =>
            ((j, l), Some(a), Map(XIn -> List(Cop1(XIn), Cop2(Some(a))), XJ -> List(Cop1(XJ))), (j, l))
          ) + (((j, l), None, Map(XIn -> List(Cop1(XIn), Cop2(None)), XJ -> List(Cop1(XJ))), (j + 1, 0)))
      }
      base
        .copy(
          states = base.states ++ newStates,
          edges = (baseEdges ++ newEdges).toSet
        )
        .renamed
    }

  }

  /** x(i) is prefix of x(j) */
  case class TakePrefix[C]() extends Transduction[C] {

    def toSolverSST(i: Int, j: Int, alphabet: Set[C]): Solver.SolverSST[C] = {
      sealed trait X
      case object XIn extends X
      case object XJ extends X
      val base = solverNsstTemplate[C, X](i, alphabet, XIn, Set(XJ), List(Cop1(XIn), Cop1(XJ), Cop2(None)))
      val states = base.states + ((j, 1))
      val variables = Set[X](XIn, XJ)
      val idUpdate = Concepts.updateMonoid[X, Option[C]](variables).unit
      val update: Map[Option[C], Concepts.Update[X, Option[C]]] =
        base.in.map(a => a -> (idUpdate + (XIn -> List(Cop1(XIn), Cop2(a))))).toMap
      val edges = {
        val baseEdges = base.edges.view.filterNot { case ((q, _), _, _, _) => q == j }
        val someEdges =
          alphabet.view.flatMap(a =>
            Iterable(
              ((j, 0), Some(a), update(Some(a)) + (XJ -> List(Cop1(XJ), Cop2(Some(a)))), (j, 0)),
              ((j, 0), Some(a), update(Some(a)), (j, 1)),
              ((j, 1), Some(a), update(Some(a)), (j, 1))
            )
          )
        val noneEdges =
          Iterable(((j, 0), None, update(None), (j + 1, 0)), ((j, 1), None, update(None), (j + 1, 0)))
        baseEdges ++ someEdges ++ noneEdges
      }
      NSST[(Int, Int), Option[C], Option[C], X](
        states,
        base.in,
        variables,
        edges.toSet,
        (0, 0),
        base.outF
      ).renamed
    }

  }

  /** x(i) is suffix of x(j) */
  case class TakeSuffix[C]() extends Transduction[C] {

    def toSolverSST(i: Int, j: Int, alphabet: Set[C]): Solver.SolverSST[C] = {
      sealed trait X
      case object XIn extends X
      case object XJ extends X
      val base = solverNsstTemplate[C, X](i, alphabet, XIn, Set(XJ), List(Cop1(XIn), Cop1(XJ), Cop2(None)))
      val states = base.states + ((j, 1))
      val variables = Set[X](XIn, XJ)
      val idUpdate = Concepts.updateMonoid[X, Option[C]](variables).unit
      val update: Map[Option[C], Concepts.Update[X, Option[C]]] =
        base.in.map(a => a -> (idUpdate + (XIn -> List(Cop1(XIn), Cop2(a))))).toMap
      val edges = {
        val baseEdges = base.edges.view.filterNot { case ((q, _), _, _, _) => q == j }
        val someEdges =
          alphabet.view.flatMap(a =>
            Iterable(
              ((j, 0), Some(a), update(Some(a)), (j, 0)),
              ((j, 0), Some(a), update(Some(a)) + (XJ -> List(Cop1(XJ), Cop2(Some(a)))), (j, 1)),
              ((j, 1), Some(a), update(Some(a)) + (XJ -> List(Cop1(XJ), Cop2(Some(a)))), (j, 1))
            )
          )
        val noneEdges =
          Iterable(((j, 0), None, update(None), (j + 1, 0)), ((j, 1), None, update(None), (j + 1, 0)))
        baseEdges ++ someEdges ++ noneEdges
      }
      NSST[(Int, Int), Option[C], Option[C], X](
        states,
        base.in,
        variables,
        edges.toSet,
        (0, 0),
        base.outF
      ).renamed
    }

  }

  /** x(i) := prefix of x(j) that excludes longet prefix of x(j) that excludes leftmost `target`.
    * If x(j) does not contain `target`, then x(i) will be x(j) followed by additional one character. */
  case class UntilFirst[C](target: Seq[C]) extends Transduction[C] {

    def toSolverSST(i: Int, j: Int, alphabet: Set[C]): Solver.SolverSST[C] = {
      type Q = (Int, Int)
      sealed trait X
      case object XIn extends X
      case object XJ extends X
      type A = Option[C]
      type B = Option[C]
      type Update = Concepts.Update[X, B]
      val base = solverNsstTemplate[C, X](i, alphabet, XIn, Set(XJ), List(Cop1(XIn), Cop1(XJ), Cop2(None)))
      val xs = base.variables
      val updates: Monoid[Update] = Concepts.updateMonoid(xs)
      val dfa = postfixDFA(target, alphabet)
      val inSet = alphabet.map(Some(_): Option[C]) + None
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
          val states = dfa.states
          // On non-final states q, when translated SST reads None, it should append to variable i
          // the prefix of target string stored in DFA that followed by one arbitrary character,
          // because no target string has been found.
          val toNext: Edges =
            (states -- dfa.finalStates).map(q => {
              val stored = target.take(q) :+ alphabet.head
              val appendStored: Update = {
                Map(
                  XIn -> List(Cop1(XIn), Cop2(None)),
                  XJ -> (List(Cop1(XJ)) ++ stored.toList.map(a => Cop2(Some(a))))
                )
              }
              ((j, q), None, appendStored, (j + 1, 0))
            })
          // On the other hand, being on final states means target has been found.
          // Thus it should keep XJ unchanged.
          val onFinal: Edges =
            for (q <- dfa.finalStates; a <- inSet)
              yield ((j, q), a, Map(XIn -> List(Cop1(XIn), Cop2(a)), XJ -> List(Cop1(XJ))), (j + 1, 0))
          // In each transition, DFA discards some (possibly empty) prefix string.
          // SST should store it in variable XJ (it should also store input char in XIn, of course).
          val edgesFromDfa: Edges = {
            for (q <- states -- dfa.finalStates; a <- alphabet)
              yield {
                val r = dfa.transition((q, a))
                val append =
                  if (dfa.finalStates contains r) Seq.empty
                  else {
                    val qStored = target.take(q) ++ List(a)
                    qStored.take(qStored.length - r).toList.map(Some(_))
                  }
                val m = updates.combine(
                  appendWordTo(XIn, xs, List(Some(a))),
                  appendWordTo(XJ, xs, append.toList)
                )
                ((j, q), Some(a), m, (j, r))
              }
          }
          edgesFromDfa ++ toNext ++ onFinal
        }
        (notFromJ ++ jthComponent)
      }
      val states = edges.map { case (q, _, _, _) => q } + ((i, 0))
      val q0 = if (j == 0) (j, dfa.q0) else (0, 0)
      NSST[Q, A, B, X](
        states,
        inSet,
        xs,
        edges,
        q0,
        base.partialF
      ).renamed
    }

  }

  case class StringVar(name: String)
  case class IntVar(name: String)

  sealed trait AtomicConstraint[A]
  case class Constant[A](lhs: StringVar, word: Seq[A]) extends AtomicConstraint[A]
  case class CatCstr[A](lhs: StringVar, rhs: Seq[Either[Seq[A], StringVar]]) extends AtomicConstraint[A]
  case class TransCstr[A](lhs: StringVar, trans: Transduction[A], rhs: StringVar) extends AtomicConstraint[A]

  sealed trait IntExp
  case class ConstExp(i: Int) extends IntExp
  case class VarExp(v: IntVar) extends IntExp
  case class LenExp(v: StringVar) extends IntExp
  case class AddExp(es: Iterable[IntExp]) extends IntExp
  case class SubExp(e1: IntExp, e2: IntExp) extends IntExp
  case class MinusExp(i: IntExp) extends IntExp

  sealed trait IntConstraint
  case class IntEq(e1: IntExp, e2: IntExp) extends IntConstraint
  case class IntLt(e1: IntExp, e2: IntExp) extends IntConstraint
  case class IntConj(cs: Iterable[IntConstraint]) extends IntConstraint
  case class IntDisj(cs: Iterable[IntConstraint]) extends IntConstraint
  case class IntNeg(c: IntConstraint) extends IntConstraint

  case class RegexConstraint[A](v: StringVar, re: RegExp[A])
  case class SLConstraint[A](
      as: Seq[AtomicConstraint[A]],
      is: Seq[IntConstraint],
      rs: Seq[RegexConstraint[A]]
  )

}

object ConstraintExamples {
  import Constraint._
  // Zhu's case 1
  val c1 = {
    val Seq(x0, x1, x2) = (0 to 2).map(i => StringVar(s"x$i"))
    val s1 = TransCstr(x1, ReplaceAll("a", "b"), x0)
    val s2 = CatCstr(x2, List(Left("a".toList), Right(x1), Left("b".toList)))
    val r = RegexConstraint(x2, CatExp(CatExp(CharExp('a'), StarExp(CharExp('b'))), CharExp('a')))
    SLConstraint(Seq(s1, s2), Nil, Seq(r))
  }
  // Zhu's case 2
  val c2 = {
    val Seq(x0, x1, x2, x3, x4) = (0 to 4).map(i => StringVar(s"x$i"))
    val s1 = TransCstr(x2, ReplaceAll("<sc>", "a"), x0)
    val s2 = TransCstr(x3, ReplaceAll("<sc>", "a"), x1)
    val s3 = CatCstr[Char](x4, List(Right(x2), Right(x3)))
    val r = RegexConstraint(x4, "a<sc>a".toSeq.map(CharExp.apply).reduce[RegExp[Char]] {
      case (e1, e2) => CatExp(e1, e2)
    })
    SLConstraint(Seq(s1, s2, s3), Nil, Seq(r))
  }
  // Involving integer constraint
  val c3 = {
    val Seq(x0, x1, x2) = (0 to 2).map(i => StringVar(s"x$i"))
    val s1 = TransCstr(x1, ReplaceAll("ab", "c"), x0)
    val s2 = TransCstr(x2, ReplaceAll("ac", "aaaa"), x1)
    val i1 = IntLt(LenExp(x0), ConstExp(5)) // x0 <= 4
    val i2 = IntLt(AddExp(Seq(LenExp(x0), ConstExp(1))), LenExp(x2)) // x0 + 2 <= x2
    SLConstraint(Seq(s1, s2), Seq(i1, i2), Nil)
  }
}
