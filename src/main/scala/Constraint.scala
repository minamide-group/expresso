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
    def toSolverSST(i: Int, j: Int, alphabet: Set[C]): Solver.SolverSST[C] = {
      sealed trait X
      case object XIn extends X
      case class XJ(x: Int) extends X
      type Q = (Int, Int)
      type A = Option[C]
      type B = Option[C]
      type Update = Concepts.Update[X, B]
      type Edges = Iterable[(Q, A, Update, Q)]
      val jsst = this.toSST(alphabet)
      val xjs: Set[X] = jsst.variables.map(XJ.apply)
      val xj = xjs.head
      val base = solverNsstTemplate[C, X](i, alphabet, XIn, xjs, List(Cop1(XIn), Cop1(xj), Cop2(None)))
      val xs = base.variables
      val updates: Monoid[Update] = Concepts.updateMonoid(xs)
      def append(b: B): Update = updates.unit + (XIn -> List(Cop1(XIn), Cop2(b)))
      val states: Set[Q] = base.states - ((j, 0)) ++ jsst.states.map((j, _))
      val edges: Edges = {
        val baseNoJ = base.edges.filter { case (q, a, m, r) => (q._1 != j) && (r._1 != j) }
        val toJ = ((j - 1, 0), None, append(None), (j, jsst.q0))
        def embedList(l: Concepts.Cupstar[Int, C]): Concepts.Cupstar[X, B] =
          l.map { case Cop1(y) => Cop1(XJ(y)); case Cop2(c) => Cop2(Some(c)) }
        def embedUpdate(m: Concepts.Update[Int, C]): Concepts.Update[X, B] =
          m.map { case (x, l) => XJ(x) -> embedList(l) }
        val withinJ: Edges = jsst.edges.map {
          case (q, a, m, r) =>
            (((j, q), Some(a), embedUpdate(m) + (XIn -> List(Cop1(XIn), Cop2(Some(a)))), (j, r)))
        }
        val fromJ: Edges =
          for ((qf, s) <- jsst.outF; l <- s)
            yield ((j, qf), None, append(None) + (xj -> embedList(l)), (j + 1, 0))

        baseNoJ + toJ ++ withinJ ++ fromJ
      }
      base
        .copy(
          states = states,
          variables = xs ++ xjs,
          edges = edges.toSet,
          q0 = if (j == 0) (j, jsst.q0) else (0, 0)
        )
        .renamed
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
      type Update = Concepts.Update[X, C]
      type Edges = Iterable[(Q, C, Update, Q)]
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
      val outF: Map[Q, Set[Concepts.Cupstar[X, C]]] = NSST.graphToMap {
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
      type Update = Concepts.Update[X, C]
      type Edges = Iterable[(Q, C, Update, Q)]
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
      val outF: Map[Q, Set[Concepts.Cupstar[X, C]]] = NSST.graphToMap {
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
      type Update = Concepts.Update[X, B]
      type Edge = (Q, A, Update, Q)
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
    * If x(j) does not contain `target`, then x(i) will be x(j) followed by additional one character. */
  case class UntilFirst[C](target: Seq[C]) extends Transduction[C] {

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      type Q = Int
      type X = Int
      type Update = Concepts.Update[X, C]
      type Edges = Iterable[(Q, C, Update, Q)]
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
      val outF: Map[Q, Set[Concepts.Cupstar[X, C]]] =
        // On each state q, DFA has partially matched prefix of target string.
        states
          .map(q =>
            q -> {
              // On non-final states q, it should append to variable
              // the prefix of target string stored in DFA that followed by one arbitrary character,
              // because no target string has been found.
              if (!dfa.finalStates(q)) {
                val stored = target.take(q) :+ alphabet.head
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
  case class TransCstr[A](lhs: StringVar, trans: Transduction[A], rhs: StringVar) extends AtomicConstraint[A]

  /**
    * Interpret terms made up from StringVar as length of them.
    */
  type IntConstraint = Presburger.Formula[Var]
  type IntExp = Presburger.Term[Var]

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
    import Presburger._
    val Seq(x0, x1, x2) = (0 to 2).map(i => StringVar(s"x$i"))
    val s1 = TransCstr(x1, ReplaceAll("ab", "c"), x0)
    val s2 = TransCstr(x2, ReplaceAll("ac", "aaaa"), x1)
    val i1: Formula[Constraint.Var] = Lt(Var(x0), Const(5)) // x0 <= 4
    val i2: Formula[Constraint.Var] = Lt(Add(Seq(Var(x0), Const(1))), Var(x2)) // x0 + 2 <= x2
    SLConstraint(Seq(s1, s2), Seq(i1, i2), Nil)
  }
}
