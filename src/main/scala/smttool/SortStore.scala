package com.github.kmn4.expresso.smttool

import smtlib.trees.Terms
import smtlib.trees.Commands

trait SortStore {
  def register(name: String, sort: Terms.Sort): Unit
  def map: Map[String, Terms.Sort]
  def mapOf(ss: Iterable[String]): Map[String, Terms.Sort]
}

object SortStore {
  // commands で declare-const, declare-fun された定数のソートを覚えた
  // SortStore を生成する
  def apply(commands: Commands.Command*): SortStore = new SortStore {

    private val sorts = collection.mutable.Map.empty[String, Terms.Sort]
    commands.foreach {
      case Commands.DeclareConst(Terms.SSymbol(name), sort) =>
        register(name, sort)
      case Commands.DeclareFun(Terms.SSymbol(name), Seq(), sort) =>
        register(name, sort)
      case t @ Commands.DeclareFun(Terms.SSymbol(_), _, _) =>
        throw new Exception(s"not supported: ${t}")
      case _ => ()
    }

    override def register(name: String, sort: Terms.Sort): Unit =
      assert(sorts.getOrElseUpdate(name, sort) == sort)

    override def map: Map[String, Terms.Sort] = sorts.toMap

    override def mapOf(ss: Iterable[String]): Map[String, Terms.Sort] =
      ss.iterator.map(s => s -> sorts(s)).toMap

  }
}
