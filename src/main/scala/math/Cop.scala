package com.github.kmn4.expresso.math

sealed trait Cop[+A, +B] extends Product with Serializable {
  def map1[C](f: A => C): Cop[C, B] = Cop.map1(this, f)
  def map2[C](f: B => C): Cop[A, C] = Cop.map2(this, f)
  def commute: Cop[B, A] = Cop.commute(this)
  def is1: Boolean
  def is2: Boolean = !is1
  def toEither: Either[A, B] = this match {
    case Cop1(a) => Left(a)
    case Cop2(b) => Right(b)
  }
}
case class Cop1[A, B](a: A) extends Cop[A, B] {
  def is1 = true
  def copy[C]: Cop1[A, C] = Cop1(a)
}
case class Cop2[A, B](b: B) extends Cop[A, B] {
  def is1 = false
  def copy[C]: Cop2[C, B] = Cop2(b)
}
object Cop {
  def flatten[A](a: Cop[A, A]): A = a match { case Cop1(a) => a; case Cop2(a) => a }
  def map1[A, B, C](ab: Cop[A, B], f: A => C): Cop[C, B] = ab match {
    case Cop1(a) => Cop1(f(a))
    case Cop2(b) => Cop2(b)
  }
  def map2[A, B, C](ab: Cop[A, B], f: B => C): Cop[A, C] = ab match {
    case Cop1(a) => Cop1(a)
    case Cop2(b) => Cop2(f(b))
  }
  def commute[A, B](ab: Cop[A, B]): Cop[B, A] = ab match {
    case Cop1(a) => Cop2(a)
    case Cop2(b) => Cop1(b)
  }
  def flatMap1[A, B, C](ab: Cop[A, B], f: A => Cop[C, B]): Cop[C, B] = ab match {
    case Cop1(a) => f(a)
    case Cop2(b) => Cop2(b)
  }
  def flatMap2[A, B, C](ab: Cop[A, B], f: B => Cop[A, C]): Cop[A, C] = ab match {
    case Cop1(a) => Cop1(a)
    case Cop2(b) => f(b)
  }
  def erase1[A, B](ab: Cop[A, B]): Option[B] = ab match {
    case Cop1(a) => None
    case Cop2(b) => Some(b)
  }
  def erase2[A, B](ab: Cop[A, B]): Option[A] = ab match {
    case Cop1(a) => Some(a)
    case Cop2(b) => None
  }
}
