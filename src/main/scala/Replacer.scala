package com.github.kmn4.sst

object Replacer {
  sealed trait PCRE[A, X] {
    // def toNFTwLA: NFTwLA[Int, A, X] = PCRE.pcreToNFTwLA(this)
    // def toNFT: NFT[Int, A, Either[A, (Option[X], Boolean)]] = {
    //   val nftwla = PCRE.pcreToNFTwLA[A, Option[X]](
    //     PCRE.Greedy(PCRE.Alt(PCRE.Group(this, None), PCRE.Chars(this.usedChars))),
    //     PCRE.Eps()
    //   )
    //   ???
    // }
    def usedChars: Set[A] = this match {
      case PCRE.Chars(as)            => as
      case PCRE.Cat(es @ _*)         => es.flatMap(_.usedChars).toSet
      case PCRE.Alt(e1, e2)          => e1.usedChars ++ e2.usedChars
      case PCRE.Greedy(e)            => e.usedChars
      case PCRE.Group(e, _)          => e.usedChars
      case PCRE.Empty() | PCRE.Eps() => Set.empty
    }
  }
  object PCRE {
    case class Empty[A, X]() extends PCRE[A, X]
    case class Eps[A, X]() extends PCRE[A, X]
    case class Chars[A, X](as: Set[A]) extends PCRE[A, X]
    case class Cat[A, X](es: PCRE[A, X]*) extends PCRE[A, X]
    case class Alt[A, X](e1: PCRE[A, X], e2: PCRE[A, X]) extends PCRE[A, X]
    case class Greedy[A, X](e: PCRE[A, X]) extends PCRE[A, X]
    case class Group[A, X](e: PCRE[A, X], x: X) extends PCRE[A, X]

    def pcreToNFTwLA[A, X](e: PCRE[A, X], cont: PCRE[A, X]): NFTwLA[Int, A, X] = {
      var _state = 0
      def freshStates(): (Int, Int) = {
        val res = (_state, _state + 1)
        _state += 2
        res
      }
      val inSet = e.usedChars
      type Edge = (Int, Option[A], Seq[Either[A, (X, Boolean)]], Map[PCRE[A, X], Boolean], Int)
      def epsEdge(q: Int, r: Int): Edge = (q, None, Seq.empty, Map.empty, r)
      def laEdge(q: Int, m: Map[PCRE[A, X], Boolean], r: Int): Edge = (q, None, Seq.empty, m, r)
      def construct(e: PCRE[A, X], cont: PCRE[A, X]): NFTwLA[Int, A, X] = e match {
        case Empty() =>
          val (q1, q2) = freshStates()
          NFTwLA(Set(q1), inSet, Map.empty, q1, q2)
        case Eps() =>
          val (q, _) = freshStates()
          NFTwLA(Set(q), inSet, Map.empty, q, q)
        case Chars(as) =>
          val (q0, qf) = freshStates()
          NFTwLA(Set(q0, qf), inSet, Map(q0 -> NonEpsEdges(as.map(_ -> qf).toMap)), q0, qf)
        case Cat(es @ _*) =>
          es.foldRight((construct(Eps(), Eps()), cont)) {
              case (e, (n2, cont)) =>
                val n1 = construct(e, cont)
                val states = n1.states ++ n2.states
                val edges = n1.edges ++ n2.edges + (n1.qf -> EpsEdge[Int, A, X](n2.q0, None))
                (
                  NFTwLA(states, inSet, edges, n1.q0, n2.qf),
                  Cat(e, cont)
                )
            }
            ._1
        case Alt(e1, e2) =>
          val (q0, qf) = freshStates()
          var states = Set(q0, qf)
          val n1 = construct(e1, cont)
          val n2 = construct(e2, cont)
          NFTwLA(
            n1.states ++ n2.states + q0 + qf,
            inSet,
            n1.edges ++ n2.edges ++ Map(
              q0 -> LAEdges(Set((n1.q0, Cat(e1, cont) -> true), (n2.q0, Cat(e1, cont) -> false))),
              n1.qf -> EpsEdge(qf, None),
              n2.qf -> EpsEdge(qf, None)
            ),
            q0,
            qf
          )
        case Greedy(e) =>
          val (q0, qf) = freshStates()
          val n = construct(e, Cat(Greedy(e), cont))
          val la: PCRE[A, X] = Cat(e, Greedy(e), cont)
          val edges = n.edges ++ Map[Int, NFTwLAEdges[Int, A, X]](
            q0 -> LAEdges(Set((n.q0, la -> true), (qf, la -> false))),
            n.qf -> EpsEdge(q0, None)
          )
          NFTwLA(n.states + q0 + qf, inSet, edges, q0, qf)
        case Group(e, x) =>
          val (q0, qf) = freshStates()
          val n = construct(e, cont)
          val edges = n.edges ++ Map[Int, NFTwLAEdges[Int, A, X]](
            q0 -> EpsEdge(n.q0, Some((x, false))),
            n.qf -> EpsEdge(qf, Some((x, true)))
          )
          NFTwLA(n.states + q0 + qf, inSet, n.edges ++ edges, q0, qf)
      }
      construct(e, cont)
    }

  }
  object Examples {
    import PCRE._
    def empty: PCRE[Char, String] = Empty()
    def eps: PCRE[Char, String] = Eps()
    def char(a: Char): PCRE[Char, String] = Chars(Set(a))
    def cat(es: PCRE[Char, String]*): PCRE[Char, String] = Cat(es: _*)
    def alt(e1: PCRE[Char, String], e2: PCRE[Char, String]): PCRE[Char, String] = Alt(e1, e2)
    def greedy(e: PCRE[Char, String]): PCRE[Char, String] = Greedy(e)
    def group(e: PCRE[Char, String], x: String): PCRE[Char, String] = Group(e, x)
    val e1 = cat(greedy(alt(char('a'), char('b'))), char('c'))
    val n1 = pcreToNFTwLA(e1, Eps())
    val nn1 = n1.toNoEpsNFTwLA
    val e2 = cat(alt(char('a'), eps), alt(eps, char('b')))
    val n2 = pcreToNFTwLA(e2, Eps())
    val nn2 = n2.toNoEpsNFTwLA
    val e3 = cat(char('a'), greedy(alt(char('b'), char('c'))))
    val n3 = pcreToNFTwLA(e3, Eps())
    val nn3 = n3.toNoEpsNFTwLA
  }

  sealed trait NFTwLAEdges[Q, A, X]
  type LA[A, X] = (PCRE[A, X], Boolean)
  // (r, la): to `r` with lookadhead `la`
  case class LAEdges[Q, A, X](rlas: Set[(Q, LA[A, X])]) extends NFTwLAEdges[Q, A, X]
  // (r, o): to `r` with output `o`
  case class EpsEdge[Q, A, X](r: Q, o: Option[(X, Boolean)]) extends NFTwLAEdges[Q, A, X]
  // a -> r: to `r` reading `a`
  case class NonEpsEdges[Q, A, X](ar: Map[A, Q]) extends NFTwLAEdges[Q, A, X]

  case class NoEpsNFTwLA[Q, A, X](
      states: Set[Q],
      inSet: Set[A],
      edges: Set[(Q, A, Seq[Either[A, (X, Boolean)]], Map[PCRE[A, X], Boolean], Q)],
      q0: Q,
      qf: Set[Q]
  )

  case class NFTwLA[Q, A, X](
      states: Set[Q],
      inSet: Set[A],
      // Some(a) for 'a', None for ε, Left(a) for 'a', Right((x, false)) for '(x', Right((x, true)) for ')x'
      edges: Map[Q, NFTwLAEdges[Q, A, X]],
      q0: Q,
      qf: Q
  ) {
    type Output = Seq[Either[A, (X, Boolean)]]
    type LAMap = Map[PCRE[A, X], Boolean]

    def toNoEpsNFTwLA: NoEpsNFTwLA[Q, A, X] = {
      case class SearchConfig(
          from: Q,
          cur: Q,
          output: Output,
          laMap: LAMap,
          readA: Option[A],
          reached: Set[Q],
          looped: Boolean
      )
      var stack: List[SearchConfig] = List(SearchConfig(q0, q0, Seq.empty, Map.empty, None, Set(q0), false))
      var newNonEpsEdges: List[(Q, A, Output, LAMap, Q)] = Nil
      var newEpsEdges: List[(Q, Output, Q)] = Nil
      def consistent(m1: LA[A, X], m2: LAMap): Boolean =
        m1 match { case (k, v) => !m2.isDefinedAt(k) || v == m2(k) }
      while (stack.nonEmpty) {
        val h = stack.head
        stack = stack.tail
        if (h.cur == qf) h.readA match {
          case Some(a) => newNonEpsEdges ::= (h.from, a, h.output, h.laMap, h.cur)
          case None    => newEpsEdges ::= (h.from, h.output, qf)
        }
        edges.get(h.cur).foreach {
          case NonEpsEdges(ar) if h.readA.nonEmpty =>
            newNonEpsEdges ::= (h.from, h.readA.get, h.output, h.laMap, h.cur)
            if (!h.looped) stack ::= SearchConfig(h.cur, h.cur, Seq.empty, Map.empty, None, h.reached, false)
          case NonEpsEdges(ar) if h.readA.isEmpty =>
            // Non-eps edge never lead back
            for ((a, r) <- ar)
              stack ::= h
                .copy(cur = r, output = h.output :+ Left(a), readA = Some(a), reached = h.reached + r)
          case LAEdges(rlas) if h.readA.nonEmpty =>
            newNonEpsEdges ::= (h.from, h.readA.get, h.output, h.laMap, h.cur)
            if (!h.looped) stack ::= SearchConfig(h.cur, h.cur, Seq.empty, Map.empty, None, h.reached, false)
          case LAEdges(rlas) if h.readA.isEmpty =>
            // lookahead edges never lead back
            for ((r, la) <- rlas if consistent(la, h.laMap))
              stack ::= h.copy(
                cur = r,
                laMap = h.laMap + la,
                reached = h.reached + r
              )
          case EpsEdge(r, o) =>
            stack ::= h
              .copy(
                cur = r,
                output = h.output ++ o.toSeq.map(Right.apply),
                reached = h.reached + r,
                looped = h.looped || h.reached(r)
              )
        }
      }
      val backNewNonEps = NSST.graphToMap(newNonEpsEdges) { case (q, a, o, la, r) => r -> (q, a, o, la) }
      for {
        (q, o2, r) <- newEpsEdges
        (p, a, o1, la) <- backNewNonEps(q)
      } newNonEpsEdges ::= (p, a, o1 ++ o2, la, r)

      NoEpsNFTwLA(
        states,
        inSet,
        newNonEpsEdges.toSet,
        q0,
        if (newEpsEdges.exists { case (q, _, r) => q == q0 && r == qf }) Set(q0, qf) else Set(qf)
      )
    }

    /** require: does not contain ε-loop */
    def toNFT: NFT[Q, A, A] = {
      case class SearchConfig(
          from: Q,
          cur: Q,
          output: Output,
          laMap: LAMap,
          passedQ0: Boolean,
          readA: Option[A]
      )
      var stack: List[SearchConfig] = List(SearchConfig(q0, q0, Seq.empty, Map.empty, false, None))
      var newNonEpsEdges: List[(Q, A, Output, LAMap, Q)] = Nil
      var newEpsEdges: List[(Q, Output, Q)] = Nil
      def consistent(m1: LA[A, X], m2: LAMap): Boolean =
        m1 match { case (k, v) => !m2.isDefinedAt(k) || v == m2(k) }
      while (stack.nonEmpty) {
        val h = stack.head
        stack = stack.tail
        if (h.cur == qf) h.readA match {
          case Some(a) => newNonEpsEdges ::= (h.from, a, h.output, h.laMap, h.cur)
          case None    => newEpsEdges ::= (h.from, h.output, qf)
        }
        edges.get(h.cur).foreach {
          case NonEpsEdges(ar) if h.readA.nonEmpty =>
            newNonEpsEdges ::= (h.from, h.readA.get, h.output, h.laMap, h.cur)
            if (!h.passedQ0) stack ::= SearchConfig(h.cur, h.cur, Seq.empty, Map.empty, false, None)
          case NonEpsEdges(ar) if h.readA.isEmpty =>
            // Non-eps edge never lead to q0
            for ((a, r) <- ar) stack ::= h.copy(cur = r, output = h.output :+ Left(a), readA = Some(a))
          case LAEdges(rlas) if h.readA.nonEmpty =>
            newNonEpsEdges ::= (h.from, h.readA.get, h.output, h.laMap, h.cur)
            if (!h.passedQ0) stack ::= SearchConfig(h.cur, h.cur, Seq.empty, Map.empty, false, None)
          case LAEdges(rlas) if h.readA.isEmpty =>
            for ((r, la) <- rlas if consistent(la, h.laMap))
              stack ::= h.copy(
                cur = r,
                laMap = h.laMap + la,
                passedQ0 = h.passedQ0 || r == q0
              )
          case EpsEdge(r, o) =>
            stack ::= h
              .copy(cur = r, output = h.output ++ o.toSeq.map(Right.apply), passedQ0 = h.passedQ0 || r == q0)
        }
      }
      val backNewNonEps = NSST.graphToMap(newNonEpsEdges) { case (q, a, o, la, r) => r -> (q, a, o, la) }
      for {
        (q, o2, r) <- newEpsEdges
        (p, a, o1, la) <- backNewNonEps(q)
      } newNonEpsEdges ::= (p, a, o1 ++ o2, la, r)
      ???
    }
  }

}
