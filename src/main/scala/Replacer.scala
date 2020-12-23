package com.github.kmn4.sst

import MonadPlus.MonadPlusOps

trait MonadPlus[M[_]] {
  def empty[T]: M[T]
  def apply[T](t: T): M[T]
  def flatMap[T, S](m: M[T])(f: T => M[S]): M[S]
  def concat[T](m: M[T], n: M[T]): M[T]
}

object MonadPlus {
  def apply[M[_]: MonadPlus] = implicitly[MonadPlus[M]]

  implicit class MonadPlusOps[M[_]: MonadPlus, T](m: M[T]) {
    def flatMap[S](f: T => M[S]): M[S] = MonadPlus[M].flatMap(m)(f)
    def concat(n: M[T]): M[T] = MonadPlus[M].concat(m, n)

    def >>=[S](f: T => M[S]): M[S] = this.flatMap(f)
    def ++(n: M[T]): M[T] = this.concat(n)

    def map[S](f: T => S): M[S] = this >>= (f andThen MonadPlus[M].apply)
  }

  implicit val seqMonadPlus = new MonadPlus[Seq] {
    def empty[T]: Seq[T] = Seq.empty
    def apply[T](t: T): Seq[T] = Seq(t)
    def flatMap[T, S](m: Seq[T])(f: T => Seq[S]): Seq[S] = m.flatMap(f)
    def concat[T](m: Seq[T], n: Seq[T]): Seq[T] = m ++ n
  }
}

sealed trait Tree[A] {
  def toSeq: Seq[A] = this match {
    case Node(a, children @ _*) => a +: children.flatMap(_.toSeq)
  }

  def toSet: Set[A] = toSeq.toSet
}
case class Node[A](a: A, children: Tree[A]*) extends Tree[A]

case class NonEmptyDistinctSeq[A](head: A, tail: Seq[A])

object Replacer {
  sealed trait Paren[X]
  case class LPar[X](x: X) extends Paren[X]
  case class RPar[X](x: X) extends Paren[X]
  type ParsedChar[A, X] = Either[A, Paren[X]]
  type Parsed[A, X] = Seq[ParsedChar[A, X]]

  sealed trait PCRE[A, X] {
    def usedChars: Set[A] = this match {
      case PCRE.Chars(as)            => as
      case PCRE.Cat(e1, e2)          => e1.usedChars ++ e2.usedChars
      case PCRE.Alt(e1, e2)          => e1.usedChars ++ e2.usedChars
      case PCRE.Greedy(e)            => e.usedChars
      case PCRE.NonGreedy(e)         => e.usedChars
      case PCRE.Group(e, _)          => e.usedChars
      case PCRE.GDeriv(e, _)         => e.usedChars
      case PCRE.Empty() | PCRE.Eps() => Set.empty
    }

    def groupVarTrees: Seq[Tree[X]] = this match {
      case PCRE.Empty() | PCRE.Eps() | PCRE.Chars(_) => Seq.empty
      case PCRE.Cat(e1, e2)                          => e1.groupVarTrees ++ e2.groupVarTrees
      case PCRE.Alt(e1, e2)                          => e1.groupVarTrees ++ e2.groupVarTrees
      case PCRE.Greedy(e)                            => e.groupVarTrees
      case PCRE.NonGreedy(e)                         => e.groupVarTrees
      case PCRE.Group(e, x)                          => Seq(Node(x, e.groupVarTrees: _*))
      case PCRE.GDeriv(e, x)                         => Seq(Node(x, e.groupVarTrees: _*))
    }

    def groupVars: Set[X] = groupVarTrees.flatMap(_.toSeq).toSet

    def derive[M[_]](a: A)(implicit mp: MonadPlus[M]): M[(Option[PCRE[A, X]], Parsed[A, X])] = this match {
      case PCRE.Empty()   => mp.empty
      case PCRE.Eps()     => mp((None, Seq.empty))
      case PCRE.Chars(as) => if (as(a)) mp.apply((Some(PCRE.Eps()), Seq(Left(a)))) else mp.empty
      case PCRE.Cat(e1, e2) =>
        e1.derive(a) >>= {
          case (Some(e), w) => mp((Some(PCRE.Cat(e, e2)), w))
          case (None, w)    => e2.derive(a) >>= { case (e, u) => mp(e, w ++ u) }
        }
      case PCRE.Alt(e1, e2) => e1.derive(a) ++ e2.derive(a)
      case PCRE.Greedy(e) =>
        val derived =
          e.derive(a) >>= [(Option[PCRE[A, X]], Parsed[A, X])] {
            case (Some(f), w) => mp((Some(PCRE.Cat(f, PCRE.Greedy(e))), w))
            case (None, w)    => mp((None, w))
          }
        derived ++ mp((None, Seq.empty))
      case PCRE.NonGreedy(e) =>
        val derived =
          e.derive(a) >>= [(Option[PCRE[A, X]], Parsed[A, X])] {
            case (Some(f), w) => mp((Some(PCRE.Cat(f, PCRE.NonGreedy(e))), w))
            case (None, w)    => mp((None, w))
          }
        mp[(Option[PCRE[A, X]], Parsed[A, X])]((None, Seq.empty)) ++ derived
      case PCRE.Group(e, x) =>
        e.derive(a) >>= {
          case (Some(e), w) => mp((Some(PCRE.GDeriv(e, x)), Right(LPar(x)) +: w))
          case (None, w)    => mp((None, Right(LPar(x)) +: w :+ Right(RPar(x))))
        }
      case PCRE.GDeriv(e, x) =>
        e.derive(a) >>= {
          case (Some(e), w) => mp((Some(PCRE.GDeriv(e, x)), w))
          case (None, w)    => mp((None, w :+ Right(RPar(x))))
        }
    }

    def matchOne[M[_]](a: A)(implicit mp: MonadPlus[M]): M[(PCRE[A, X], Parsed[A, X])] = derive(a) >>= {
      case (Some(e), w) => mp((e, w))
      case (None, _)    => mp.empty
    }

    def matchSeq[M[_]](as: Seq[A])(implicit mp: MonadPlus[M]): M[(PCRE[A, X], Parsed[A, X])] =
      as.foldLeft(mp((this, Seq.empty[ParsedChar[A, X]]))) {
        case (m, a) => m >>= { case (e, w) => e.matchOne(a) map { case (e, u) => (e, w ++ u) } }
      }

    def deriveEps[M[_]](implicit mp: MonadPlus[M]): M[Parsed[A, X]] = this match {
      case PCRE.Empty() | PCRE.Chars(_) => mp.empty
      case PCRE.Eps()                   => mp(Seq.empty)
      case PCRE.Cat(e1, e2)             => for (w <- e1.deriveEps; u <- e2.deriveEps) yield w ++ u
      case PCRE.Alt(e1, e2)             => e1.deriveEps ++ e2.deriveEps
      case PCRE.Greedy(e)               => e.deriveEps ++ mp(Seq.empty)
      case PCRE.NonGreedy(e)            => mp(Seq.empty)
      case PCRE.Group(e, x)             => e.deriveEps.map(Right(LPar(x)) +: _ :+ Right(RPar(x)))
      case PCRE.GDeriv(e, x)            => e.deriveEps.map(_ :+ Right(RPar(x)))
    }

    def toParser(alphabet: Set[A]): NSST[NonEmptyDistinctSeq[PCRE[A, X]], A, ParsedChar[A, X], Unit] = {
      require(usedChars subsetOf alphabet)
      type Q = NonEmptyDistinctSeq[PCRE[A, X]]
      val q0 = NonEmptyDistinctSeq(this, Seq.empty)
      def nextStates(q: Q, a: A): Set[(Q, Parsed[A, X])] = {
        val NonEmptyDistinctSeq(lowest, highers) = q
        // In [..., (e, w1), ..., (e, w2), ...], (e, w2) will never be taken as parse result.
        // distinctBy(_._1) removes this.

        // Expressions with higher precedences.
        val nextHighers = (highers.reverse >>= (_.matchOne(a))).map(_._1).distinct.reverse
        @scala.annotation.tailrec
        def aux(acc: Set[(Q, Parsed[A, X])], l: Seq[(PCRE[A, X], Parsed[A, X])]): Set[(Q, Parsed[A, X])] =
          l match {
            case Nil                                    => acc
            case (e, w) :: tl if nextHighers contains e => aux(acc, tl)
            case (hd @ (e, w)) :: tl =>
              val newQ = NonEmptyDistinctSeq(e, tl.map(_._1) ++ nextHighers)
              aux(acc + ((newQ, w)), tl)
          }
        aux(Set.empty, lowest.matchOne(a).distinctBy(_._1).reverse)
      }
      val (states, edges) = searchStates(Set(q0), alphabet)(nextStates)(
        { case (r, _)         => r },
        { case (q, a, (r, w)) => (q, a, w, r) }
      )
      val outGraph = for {
        q @ NonEmptyDistinctSeq(lowest, highers) <- states if highers.forall(_.deriveEps.isEmpty)
        w <- lowest.deriveEps.headOption
      } yield q -> w
      NSST(
        states,
        alphabet,
        Set(()),
        edges.map { case (q, a, w, r) => (q, a, Map(() -> (Cop1(()) +: w.map(Cop2.apply)).toList), r) },
        q0,
        graphToMap(outGraph.map {
          case (q, w) => q -> (Cop1(()) +: w.map(Cop2.apply)).toList
        })(identity)
      )
    }

    override def toString(): String = this match {
      case PCRE.Empty() => "∅"
      case PCRE.Eps()   => ""
      case PCRE.Chars(as) =>
        as.size match {
          case 0 => "[∅]"
          case 1 => as.head.toString()
          case _ => s"[${as.mkString}]"
        }
      case PCRE.Cat(e1, e2) => s"$e1$e2"
      case PCRE.Alt(e1, e2) => s"$e1|$e2"
      case PCRE.Greedy(e) =>
        val s = e.toString()
        if (s.length == 1) s"$e*"
        else s"($e)*"
      case PCRE.NonGreedy(e) =>
        val s = e.toString()
        if (s.length == 1) s"$e*?"
        else s"($e)*?"
      case PCRE.Group(e, x)  => s"(?<$x>$e)"
      case PCRE.GDeriv(e, x) => s"<?<$x>$e>"
    }

    def renameVars[Y](f: X => Y): PCRE[A, Y] = this match {
      case PCRE.Group(e, x)  => PCRE.Group(e.renameVars(f), f(x))
      case PCRE.GDeriv(e, x) => PCRE.GDeriv(e.renameVars(f), f(x))
      case PCRE.Empty()      => PCRE.Empty()
      case PCRE.Eps()        => PCRE.Eps()
      case PCRE.Chars(as)    => PCRE.Chars(as)
      case PCRE.Cat(e1, e2)  => PCRE.Cat(e1.renameVars(f), e2.renameVars(f))
      case PCRE.Alt(e1, e2)  => PCRE.Alt(e1.renameVars(f), e2.renameVars(f))
      case PCRE.Greedy(e)    => PCRE.Greedy(e.renameVars(f))
      case PCRE.NonGreedy(e) => PCRE.NonGreedy(e.renameVars(f))
    }
  }

  object PCRE {
    case class Empty[A, X]() extends PCRE[A, X]
    case class Eps[A, X]() extends PCRE[A, X]
    case class Chars[A, X](as: Set[A]) extends PCRE[A, X]
    case class Cat[A, X](e1: PCRE[A, X], e2: PCRE[A, X]) extends PCRE[A, X]
    case class Alt[A, X](e1: PCRE[A, X], e2: PCRE[A, X]) extends PCRE[A, X]
    case class Greedy[A, X](e: PCRE[A, X]) extends PCRE[A, X]
    case class NonGreedy[A, X](e: PCRE[A, X]) extends PCRE[A, X]
    case class Group[A, X](e: PCRE[A, X], x: X) extends PCRE[A, X]
    // Derivatives of group expressions.
    case class GDeriv[A, X](e: PCRE[A, X], x: X) extends PCRE[A, X]
  }

  case class Replacement[A, X](word: Seq[Either[A, Option[X]]]) {
    def groupVars: Set[X] = word.collect { case Right(Some(x)) => x }.toSet
    lazy val indexed: Seq[Either[A, (Option[X], Int)]] = word
      .foldLeft((0, Seq.empty[Either[A, (Option[X], Int)]])) {
        case ((cur, acc), Left(a))  => (cur, Left(a) +: acc)
        case ((cur, acc), Right(x)) => (cur + 1, (Right(x, cur)) +: acc)
      }
      ._2
      .reverse
  }

  def firstMatch[A, X](e: PCRE[A, X], alphabet: Set[A]): PCRE[A, Option[X]] = {
    val renamed: PCRE[A, Option[X]] = e.renameVars(x => Some(x))
    // .*?(e).*
    PCRE.Cat(
      PCRE.Cat(PCRE.NonGreedy(PCRE.Chars(alphabet)), PCRE.Group(renamed, None)),
      PCRE.Greedy(PCRE.Chars(alphabet))
    )
  }

  def repetitiveMatch[A, X](e: PCRE[A, X], alphabet: Set[A]): PCRE[A, Option[X]] = {
    val renamed: PCRE[A, Option[X]] = e.renameVars(x => Some(x))
    // (?:(e)|.)*
    PCRE.Greedy(PCRE.Alt(PCRE.Group(renamed, None), PCRE.Chars(alphabet)))
  }

  // def replaceSST[A, X](re: PCRE[A, X], rep: Replacement[A, X]): NSST[Set[X]] = {
  //   ???
  // }
  object Compiler {
    private type SSTQ[X] = Set[Option[X]]
    private sealed trait SSTVar[X]
    private case class Out[X]() extends SSTVar[X]
    private case class Rep[X](x: Option[X], i: Int) extends SSTVar[X]

    def replaceSST[A, X](
        re: PCRE[A, X],
        rep: Replacement[A, X],
        alphabet: Set[A]
    ): NSST[Int, A, A, Int] = {
      val repetitiveRE = repetitiveMatch(re, alphabet)
      val repetitiveParser = repetitiveRE.toParser(alphabet)
      repetitiveParser compose oneTimeReplaceSST(re, rep, alphabet)
    }

    def replaceAllSST[A, X](
        re: PCRE[A, X],
        rep: Replacement[A, X],
        alphabet: Set[A]
    ): NSST[Int, A, A, Int] = {
      val repetitiveRE = repetitiveMatch(re, alphabet)
      val repetitiveParser = repetitiveRE.toParser(alphabet)
      repetitiveParser compose repetitiveReplaceSST(re, rep, alphabet)
    }

    private def repetitiveReplaceSST[A, X](
        re: PCRE[A, X],
        rep: Replacement[A, X],
        alphabet: Set[A]
    ): NSST[SSTQ[X], ParsedChar[A, Option[X]], A, SSTVar[X]] = {
      require(rep.groupVars subsetOf re.groupVars)
      type UpdateVar = Update[SSTVar[X], A]
      type Edge = (SSTQ[X], ParsedChar[A, Option[X]], UpdateVar, SSTQ[X])
      val repXs = rep.indexed.collect { case Right((x, i)) => Rep(x, i) }
      val sstVars: Set[SSTVar[X]] = repXs.toSet + Out()
      val updates: Monoid[UpdateVar] = updateMonoid(sstVars)
      def aux(parent: SSTQ[X], varsTree: Tree[Option[X]]): (Set[SSTQ[X]], Set[Edge]) =
        varsTree match {
          case Node(x, children @ _*) =>
            val cur = parent + x
            val newEdges: Set[Edge] = {
              val fromParen: Edge = {
                val shouldClear = repXs.filter { case Rep(y, i) => y == x }
                val update = updates.unit ++ shouldClear.map(x => x -> Nil)
                (parent, Right(LPar(x)), update, cur)
              }
              val loops: Iterable[Edge] = {
                val shouldUpdate = repXs.filter { case Rep(y, i) => cur(y) }
                def update(a: A) = updates.unit ++ shouldUpdate.map(x => x -> List(Cop1(x), Cop2(a)))
                alphabet.map(a => (cur, Left(a), update(a), cur))
              }
              val toParent: Edge = {
                val zero: UpdateVar = sstVars.map(x => x -> Nil).toMap
                val update: UpdateVar = if (x == None) zero + (Out() -> (Cop1(Out[X]()) +: rep.indexed.map {
                  case Right((x, i)) => Cop1(Rep(x, i))
                  case Left(a)       => Cop2(a)
                }).toList)
                else updates.unit
                (cur, Right(RPar(x)), update, parent)
              }
              loops.toSet + fromParen + toParent
            }
            val (childStates, childEdges) = children.foldLeft((Set.empty[SSTQ[X]], Set.empty[Edge])) {
              case ((accQ, accE), child) =>
                val (qs, es) = aux(cur, child)
                (accQ ++ qs, accE ++ es)
            }
            (childStates + cur, childEdges ++ newEdges)
        }
      val q0: SSTQ[X] = Set.empty
      val repetitiveRE = repetitiveMatch(re, alphabet)
      val varsTree = repetitiveRE.groupVarTrees.head
      val (states, edges) = aux(q0, varsTree)
      val q0Loop: Iterable[Edge] = {
        def update(a: A): UpdateVar = updates.unit + (Out() -> List(Cop1(Out()), Cop2(a)))
        alphabet.map(a => (q0, Left(a), update(a), q0))
      }
      NSST[SSTQ[X], ParsedChar[A, Option[X]], A, SSTVar[X]](
        states + q0,
        varsTree.toSet.flatMap(x => Set(Right(LPar(x)), Right(RPar(x)))) ++ alphabet.map(Left.apply),
        sstVars,
        edges ++ q0Loop,
        q0,
        Map(q0 -> Set(List[Cop[SSTVar[X], A]](Cop1(Out()))))
      )
    }
    // state Cop1(s): vars in s is opened, Cop2(false): initial state, Cop2(true): already replaced once
    private def oneTimeReplaceSST[A, X](
        re: PCRE[A, X],
        rep: Replacement[A, X],
        alphabet: Set[A]
    ): NSST[Cop[Set[Option[X]], Boolean], ParsedChar[A, Option[X]], A, SSTVar[X]] = {
      type Q = Cop[Set[Option[X]], Boolean]
      type U = Update[SSTVar[X], A]
      type E = (Q, ParsedChar[A, Option[X]], U, Q)
      val repetitive = repetitiveReplaceSST(re, rep, alphabet)
      val q0 = Cop2(false)
      val qf = Cop2(true)
      val states = repetitive.states.collect[Q] { case s if s.nonEmpty => Cop1(s) } + q0 + qf
      val unitUpdate = {
        val repXs = rep.indexed.collect { case Right((x, i)) => Rep(x, i) }
        updateMonoid[SSTVar[X], A](repXs.toSet + Out()).unit
      }
      val edges = repetitive.edges.map[E] {
        case (q, a, m, r) if q == Set.empty => (q0, a, m, Cop1(r))
        case (q, a, m, r) if r == Set.empty => (Cop1(q), a, m, qf)
        case (q, a, m, r)                   => (Cop1(q), a, m, Cop1(r))
      } ++ repetitive.in.collect[E] { // loop in qf
        case Left(a)  => (qf, Left(a), unitUpdate + (Out() -> List(Cop1(Out()), Cop2(a))), qf)
        case Right(p) => (qf, Right(p), unitUpdate + (Out() -> List(Cop1(Out()))), qf)
      }
      repetitive.copy(
        states = states,
        edges = edges,
        q0 = q0,
        partialF = Map(q0 -> Set(List(Cop1(Out()))), qf -> Set(List(Cop1(Out()))))
      )
    }

  }

  case class ReplacePCREAll[A, X](target: PCRE[A, X], replacement: Replacement[A, X])
      extends Constraint.Transduction[A] {

    override def usedAlphabet: Set[A] = target.usedChars

    override def toSST(alphabet: Set[A]): NSST[Int, A, A, Int] =
      Compiler.replaceAllSST(target, replacement, alphabet)

  }

  case class ReplacePCRE[A, X](target: PCRE[A, X], replacement: Replacement[A, X])
      extends Constraint.Transduction[A] {

    override def usedAlphabet: Set[A] = target.usedChars

    override def toSST(alphabet: Set[A]): NSST[Int, A, A, Int] =
      Compiler.replaceSST(target, replacement, alphabet)
  }
}
