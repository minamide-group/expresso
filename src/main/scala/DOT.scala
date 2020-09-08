package com.github.kmn4.sst

// simplified syntax of DOT
object DOT {
  type ID = String

  private def quote(s: String) = '"' + s.replace("\"", "\\\"") + '"'

  case class Attribute(name: ID, value: ID) {
    // \" instead of ${'"'} does not compile due to https://github.com/scala/bug/issues/6476
    override def toString = s"$name=${quote(value)}"
  }

  private def attrLsToString(ls: List[Attribute]) = ls match {
    case Nil => ""
    case fst :: rst =>
      val s = rst.foldLeft(fst.toString)({ case (acc, a) => s"$acc,${a.toString}" })
      s"[$s]"
  }

  sealed trait Stmt

  case class NodeStmt(id: ID, attr: List[Attribute]) extends Stmt {
    override def toString = s"${quote(id)}${attrLsToString(attr)};"
  }

  case class EdgeStmt(src: ID, dst: ID, attr: List[Attribute]) extends Stmt {
    override def toString = s"${quote(src)}->${quote(dst)}${attrLsToString(attr)};"
  }

  case class GraphSpec(name: ID, stmts: List[Stmt]) {
    override def toString = s"digraph $name {${stmts.foldLeft("")({ case (acc, s) => acc + s.toString })}}"
  }

}

trait DOTMaker[T] {
  def toDOT: DOT.GraphSpec
}

object DOTMaker {

  implicit def enrichDFA[Q, A](dfa: DFA[Q, A]): DOTMaker[DFA[Q, A]] = new DOTMaker[DFA[Q, A]] {
    def toDOT: DOT.GraphSpec = dfa.asNFA.toDOT
  }

  implicit def enrichNSST[Q, A, B, X](nsst: NSST[Q, A, B, X])
      : DOTMaker[NSST[Q, A, B, X]] = new DOTMaker[NSST[Q, A, B, X]] {
    def toDOT: DOT.GraphSpec = nsst.asNFA.toDOT
  }

  implicit def enrichNFA[Q, A](nfa: NFA[Q, A]): DOTMaker[NFA[Q, A]] = new DOTMaker[NFA[Q, A]] {
    def toDOT: DOT.GraphSpec = {
      import DOT._
      val nodeStmts: List[NodeStmt] =
        nfa.states.map(st => {
          var attr: List[Attribute] = Nil
          if (nfa.finalStates contains st) attr ::= Attribute("peripheries", "2")
          if (st == nfa.q0) attr ::= Attribute("style", "filled")
          NodeStmt(st.toString, attr)
        }).toList
      val edgeStmts: List[EdgeStmt] =
        nfa.transition.flatMap({ case ((from, a), toes) =>
          toes.map(to => EdgeStmt(
            from.toString,
            to.toString,
            List(Attribute("label", {
              a match {
                case None => "ε"
                case Some(a) => a.toString
              }
            }))))
        }).toList
      DOT.GraphSpec("main", nodeStmts ++ edgeStmts)
    }
  }
}
