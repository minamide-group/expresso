package com.github.kmn4.sst

sealed trait Cop[+A, +B] {
  def map1[C](f: A => C): Cop[C, B] = Cop.map1(this, f)
  def map2[C](f: B => C): Cop[A, C] = Cop.map2(this, f)
  def commute: Cop[B, A] = Cop.commute(this)
}
case class Cop1[A, T <: A](a: T) extends Cop[A, Nothing]
case class Cop2[B, T <: B](b: T) extends Cop[Nothing, B]
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