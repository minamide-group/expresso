package com.github.kmn4.sst

sealed trait RegExp[+A]
case object EmptyExp extends RegExp[Nothing]
case object EpsExp extends RegExp[Nothing]
case object DotExp extends RegExp[Nothing]
case class CharExp[A, B <: A](b: B) extends RegExp[A]
case class OrExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class CatExp[A, B <: A](b1: RegExp[B], b2: RegExp[B]) extends RegExp[A]
case class StarExp[A, B <: A](b: RegExp[B]) extends RegExp[A]
case class CompExp[A, B <: A](b: RegExp[B]) extends RegExp[A]
