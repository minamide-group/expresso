package com.github.kmn4.expresso.language

import com.github.kmn4.expresso._
import com.github.kmn4.expresso.math._
import com.github.kmn4.expresso.math.MonadPlus.MonadPlusOps
import com.github.kmn4.expresso.machine._

/** グループ変数 X で添字付けられたキャプチャグループの括弧 */
private sealed trait Paren[X]
private case class LPar[X](x: X) extends Paren[X]
private case class RPar[X](x: X) extends Paren[X]

sealed trait PCRE[A, X] {
  private[language] type ParsedChar = Either[A, Paren[X]]
  private[language] type Parsed = Seq[ParsedChar]

  def usedChars: Set[A] = this match {
    case PCRE.Chars(as)                             => as
    case PCRE.Cat(e1, e2)                           => e1.usedChars ++ e2.usedChars
    case PCRE.Alt(e1, e2)                           => e1.usedChars ++ e2.usedChars
    case PCRE.Greedy(e)                             => e.usedChars
    case PCRE.NonGreedy(e)                          => e.usedChars
    case PCRE.Group(e, _)                           => e.usedChars
    case PCRE.GDeriv(e, _)                          => e.usedChars
    case PCRE.Empty() | PCRE.Eps() | PCRE.AllChar() => Set.empty
  }

  private[language] def groupVarTrees: Seq[Tree[X]] = this match {
    case PCRE.Empty() | PCRE.Eps() | PCRE.Chars(_) | PCRE.AllChar() => Seq.empty
    case PCRE.Cat(e1, e2)                                           => e1.groupVarTrees ++ e2.groupVarTrees
    case PCRE.Alt(e1, e2)                                           => e1.groupVarTrees ++ e2.groupVarTrees
    case PCRE.Greedy(e)                                             => e.groupVarTrees
    case PCRE.NonGreedy(e)                                          => e.groupVarTrees
    case PCRE.Group(e, x)                                           => Seq(Node(x, e.groupVarTrees: _*))
    case PCRE.GDeriv(e, x)                                          => Seq(Node(x, e.groupVarTrees: _*))
  }

  def groupVars: Set[X] = groupVarTrees.flatMap(_.toSeq).toSet

  private def derive[M[_]](a: A)(implicit mp: MonadPlus[M]): M[(Option[PCRE[A, X]], Parsed)] =
    this match {
      case PCRE.Empty()   => mp.empty
      case PCRE.Eps()     => mp((None, Seq.empty))
      case PCRE.Chars(as) => if (as(a)) mp.apply((Some(PCRE.Eps()), Seq(Left(a)))) else mp.empty
      case PCRE.AllChar() => mp.apply((Some(PCRE.Eps()), Seq(Left(a))))
      case PCRE.Cat(e1, e2) =>
        e1.derive(a) >>= {
          case (Some(e), w) => mp((Some(PCRE.Cat(e, e2)), w))
          case (None, w)    => e2.derive(a) >>= { case (e, u) => mp(e, w ++ u) }
        }
      case PCRE.Alt(e1, e2) => e1.derive(a) ++ e2.derive(a)
      case PCRE.Greedy(e) =>
        val derived =
          e.derive(a) >>= [(Option[PCRE[A, X]], Parsed)] {
            case (Some(f), w) => mp((Some(PCRE.Cat(f, PCRE.Greedy(e))), w))
            case (None, w)    => mp((None, w))
          }
        derived ++ mp((None, Seq.empty))
      case PCRE.NonGreedy(e) =>
        val derived =
          e.derive(a) >>= [(Option[PCRE[A, X]], Parsed)] {
            case (Some(f), w) => mp((Some(PCRE.Cat(f, PCRE.NonGreedy(e))), w))
            case (None, w)    => mp((None, w))
          }
        mp[(Option[PCRE[A, X]], Parsed)]((None, Seq.empty)) ++ derived
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

  private def matchOne[M[_]](a: A)(implicit mp: MonadPlus[M]): M[(PCRE[A, X], Parsed)] =
    derive(a) >>= {
      case (Some(e), w) => mp((e, w))
      case (None, _)    => mp.empty
    }

  private def matchSeq[M[_]](as: Seq[A])(implicit mp: MonadPlus[M]): M[(PCRE[A, X], Parsed)] =
    as.foldLeft(mp((this, Seq.empty[ParsedChar]))) {
      case (m, a) => m >>= { case (e, w) => e.matchOne(a) map { case (e, u) => (e, w ++ u) } }
    }

  private def deriveEps[M[_]](implicit mp: MonadPlus[M]): M[Parsed] = this match {
    case PCRE.Empty() | PCRE.Chars(_) | PCRE.AllChar() => mp.empty
    case PCRE.Eps()                                    => mp(Seq.empty)
    case PCRE.Cat(e1, e2)                              => for (w <- e1.deriveEps; u <- e2.deriveEps) yield w ++ u
    case PCRE.Alt(e1, e2)                              => e1.deriveEps ++ e2.deriveEps
    case PCRE.Greedy(e)                                => e.deriveEps ++ mp(Seq.empty)
    case PCRE.NonGreedy(e)                             => mp(Seq.empty)
    case PCRE.Group(e, x)                              => e.deriveEps.map(Right(LPar(x)) +: _ :+ Right(RPar(x)))
    case PCRE.GDeriv(e, x)                             => e.deriveEps.map(_ :+ Right(RPar(x)))
  }

  private[language] def toParser(
      alphabet: Set[A]
  ): NGSM[NonEmptyDistinctSeq[PCRE[A, X]], A, ParsedChar] = {
    require(usedChars subsetOf alphabet)
    type Q = NonEmptyDistinctSeq[PCRE[A, X]]
    val q0 = NonEmptyDistinctSeq(this, Seq.empty)
    def nextStates(q: Q, a: A): Set[(Q, Parsed)] = {
      val NonEmptyDistinctSeq(lowest, highers) = q
      // In [..., (e, w1), ..., (e, w2), ...], (e, w2) will never be taken as parse result.
      // distinctBy(_._1) removes this.

      // Expressions with higher precedences.
      val nextHighers = (highers.reverse >>= (_.matchOne(a))).map(_._1).distinct.reverse
      @scala.annotation.tailrec
      def aux(acc: Set[(Q, Parsed)], l: Seq[(PCRE[A, X], Parsed)]): Set[(Q, Parsed)] =
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
    NGSM(
      states,
      alphabet,
      edges,
      q0,
      outGraph
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
    case PCRE.AllChar()   => "."
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
    case PCRE.AllChar()    => PCRE.AllChar()
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
  case class AllChar[A, X]() extends PCRE[A, X]
}
