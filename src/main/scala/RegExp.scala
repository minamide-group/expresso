package com.github.kmn4.sst

sealed trait RegExp[+A] {
  def usedAlphabet[B >: A]: Set[B] = this match {
    case EmptyExp | EpsExp | DotExp => Set.empty
    case CharExp(c)                 => Set(c)
    case CatExp(e1, e2)             => e1.usedAlphabet ++ e2.usedAlphabet
    case OrExp(e1, e2)              => e1.usedAlphabet ++ e2.usedAlphabet
    case StarExp(e)                 => e.usedAlphabet
    case CompExp(e)                 => e.usedAlphabet
  }

  def toNFA[B >: A](alphabet: Set[B]): NFA[Int, B] = new RegExp2NFA(this, alphabet).construct()
}
case object EmptyExp extends RegExp[Nothing]
case object EpsExp extends RegExp[Nothing]
case object DotExp extends RegExp[Nothing]
case class CharExp[A, B <: A](b: B) extends RegExp[A]
case class OrExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class CatExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class StarExp[A, B <: A](b: RegExp[B]) extends RegExp[A]
case class CompExp[A, B <: A](b: RegExp[B]) extends RegExp[A]
