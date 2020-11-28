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
            case (Some(f), w) => mp((Some(PCRE.Cat(f, PCRE.Greedy(e))), w))
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

    def deriveEps: Option[Parsed[A, X]] = this match {
      case PCRE.Empty() | PCRE.Chars(_) => None
      case PCRE.Eps()                   => Some(Seq.empty)
      case PCRE.Cat(e1, e2)             => for (w <- e1.deriveEps; u <- e2.deriveEps) yield w ++ u
      case PCRE.Alt(e1, e2)             => e1.deriveEps.orElse(e2.deriveEps)
      case PCRE.Greedy(e)               => e.deriveEps.orElse(Some(Seq.empty))
      case PCRE.NonGreedy(e)            => Some(Seq.empty)
      case PCRE.Group(e, x)             => e.deriveEps.map(Right(LPar(x)) +: _ :+ Right(RPar(x)))
      case PCRE.GDeriv(e, x)            => e.deriveEps.map(_ :+ Right(RPar(x)))
    }

    case class NonEmptyDistinctSeq[A](head: A, tail: Seq[A])
    def toParser: NSST[NonEmptyDistinctSeq[PCRE[A, X]], A, ParsedChar[A, X], Unit] = {
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
      val (states, edges) = Concepts.searchStates(Set(q0), this.usedChars)(nextStates)(
        { case (r, _)         => r },
        { case (q, a, (r, w)) => (q, a, w, r) }
      )
      val outGraph = for {
        q @ NonEmptyDistinctSeq(lowest, highers) <- states if highers.forall(_.deriveEps.isEmpty)
        w <- lowest.deriveEps
      } yield q -> w
      NSST(
        states,
        usedChars,
        Set(()),
        edges.map { case (q, a, w, r) => (q, a, Map(() -> (Cop1(()) +: w.map(Cop2.apply)).toList), r) },
        q0,
        NSST.graphToMap(outGraph.map {
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
        if (s.length == 1) s"$e*"
        else s"($e)*?"
      case PCRE.Group(e, x)  => s"(?<$x>$e)"
      case PCRE.GDeriv(e, x) => s"<?<$x>$e>"
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
}
