package com.github.kmn4.sst

import org.scalatest.flatspec._

class TestSolving extends AnyFlatSpec {
  def cupstarOf(xs: Set[Char], s: String): Concepts.Cupstar[Char, Char] =
    s.map(c => if (xs contains c) Cop1(c) else Cop2(c)).toList
  def updateOf(
      xs: Set[Char],
      m: Map[Char, String]
  ): Concepts.Update[Char, Char] =
    xs.map(x => x -> cupstarOf(xs, m.getOrElse(x, x.toString()))).toMap
  def createNSST(
      states: Set[Int],
      in: Set[Char],
      xs: Set[Char],
      edges: List[(Int, Char, Int, Map[Char, String])],
      q0: Int,
      f: Map[Int, Set[String]]
  ) = new NSST(
    states,
    in,
    xs,
    edges
      .groupBy { case (q, a, _, _) => (q, a) }
      .map {
        case (k, l) =>
          k -> l.map { case (_, _, r, m) => (r, updateOf(xs, m)) }.toSet
      },
    q0,
    f.view.mapValues(_.map(cupstarOf(xs, _))).toMap
  )
  "Zhu's experiment case 1" should "be sat" in {
    val s1 = createNSST(
      Set(0, 1),
      Set('a', 'b', '#'),
      Set('0', '1'),
      List(
        (0, 'a', 0, Map('0' -> "0a", '1' -> "1b")),
        (0, 'b', 0, Map('0' -> "0b", '1' -> "1b")),
        (0, '#', 1, Map.empty)
      ),
      0,
      Map(1 -> Set("0#1#"))
    )
    val s2 = createNSST(
      Set(0, 1, 2),
      Set('a', 'b', '#'),
      Set('0', '1', '2'),
      List(
        (0, 'a', 0, Map('0' -> "0a")),
        (0, 'b', 0, Map('0' -> "0b")),
        (0, '#', 1, Map.empty),
        (1, 'a', 1, Map('1' -> "1a", '2' -> "2a")),
        (1, 'b', 1, Map('1' -> "1b", '2' -> "2b")),
        (1, '#', 2, Map('2' -> "a2a"))
      ),
      0,
      Map(2 -> Set("0#1#2#"))
    )
    val s3 = createNSST(
      Set(0, 1, 2, 3, 4, 5),
      Set('a', 'b', '#'),
      Set('0', '1', '2'),
      List(
        (0, 'a', 0, Map('0' -> "0a")),
        (0, 'b', 0, Map('0' -> "0b")),
        (0, '#', 1, Map.empty),
        (1, 'a', 1, Map('1' -> "1a")),
        (1, 'b', 1, Map('1' -> "1b")),
        (1, '#', 2, Map.empty),
        (2, 'a', 3, Map('2' -> "2a")),
        (3, 'b', 3, Map('2' -> "2b")),
        (3, 'a', 4, Map('2' -> "2a")),
        (4, '#', 5, Map.empty)
      ),
      0,
      Map(5 -> Set("0#1#2#"))
    )
    // (s3 s2) s1, rather than s3 (s2 s1)
    val start = System.nanoTime()
    val t1 = NSST.composeNsstOfNssts(s2, s3)
    val t2 = NSST.composeNsstOfNssts(s1, t1)
    info(s"elapsed:\t${(System.nanoTime() - start) / 1000000} ms")
    info(s"states:\t${t2.states.size}")
    info(s"variables:\t${t2.variables.size}")
    info(s"transition:\t${t2.edges.size}")
    assert(t2.transduce("aba#".toList) == Set("aba#bbb#abbba#".toList))
  }

  // Construct DFA which accepts strings whose postfix is target.
  // Each state i represents target.substring(0, i).
  private def postfixDFA(target: String, in: Set[Char]) = {
    // KMP backtracking table
    val table: Vector[Int] = {
      var t = Vector(-1)
      for (i <- 1 until target.length) {
        val prev = t(i - 1)
        t = t.appended(prev + (if (target(i - 1) == target(prev + 1)) 1 else 0))
      }
      t
    }
    val states = Set.from(0 to target.length)
    val q0 = 0
    val qf = target.length
    val delta = Map.from {
      for (q <- states; a <- in if q != qf)
        yield (q, a) -> {
          var j = q
          while (j >= 0 && a != target(j)) {
            j = table(j)
          }
          j + 1
        }
    }
    new DFA(
      states,
      in,
      delta,
      q0,
      Set(qf)
    )
  }
  // Returns update which appends `w` to variable `x`, and is identity on other variables in `xs`.
  def appendWordTo[X, A](x: X, xs: Set[X], w: List[A]): Concepts.Update[X, A] =
    xs.map(y =>
        y -> (List(Cop1(y)) ++ (if (y == x) w.map(Cop2(_)) else Nil))
      )
      .toMap
  // Construct NSST which replaces `target` in `j`-th input string with `word`,
  // and output it as `i`-th string.
  def replaceAllNSST(
      target: String,
      word: String,
      i: Int,
      j: Int,
      in: Set[Char]
  ): NSST[Int, Option[Char], Option[Char], Int] = {
    if (i <= j) {
      throw new Exception()
    }
    // States of the form Cop1(q) are the states of j-th component.
    type Q = Cop[Int, Int]
    type X = Int
    type A = Option[Char]
    type B = Option[Char]
    type Update = Concepts.Update[X, B]
    val xs = Set.from(0 to i)
    val monoid: Monoid[Update] = Concepts.updateMonoid(xs)
    val dfa = postfixDFA(target, in)
    val edges: Map[(Q, A), Set[(Q, Update)]] = {
      val notFromJ: Map[(Q, A), Set[(Q, Update)]] = {
        val states = (0 until i).withFilter(_ != j)
        val loop: Map[(Q, A), Set[(Q, Update)]] = Map.from {
          for (q <- states; a <- in)
            yield (Cop2(q), Some(a)) -> Set(
              (Cop2(q), appendWordTo(q, xs, List(Some(a))))
            )
        }
        val toNext: Map[(Q, A), Set[(Q, Update)]] = Map.from {
          for (q <- states)
            yield (Cop2(q), None) -> {
              val next = if (q == j - 1) Cop1(dfa.q0) else Cop2(q + 1)
              Set((next, monoid.unit))
            }
        }
        (loop ++ toNext).toMap
      }
      val jthComponent: Map[(Q, A), Set[(Q, Update)]] = Map.from {
        val states = dfa.states -- dfa.finalStates
        val toNext: Map[(Q, A), Set[(Q, Update)]] =
          states
            .map[((Q, A), Set[(Q, Update)])](q =>
              (Cop1(q), None) ->
                Set(
                  (
                    Cop2(j + 1),
                    appendWordTo(
                      i,
                      xs,
                      target.substring(0, q).toList.map(a => Some(a))
                    )
                  )
                )
            )
            .toMap
        val edgesFromDfa: Map[(Q, A), Set[(Q, Update)]] = Map.from {
          for (q <- states; a <- in)
            yield (Cop1(q), Some(a)) -> Set {
              val t = dfa.transition((q, a))
              val (r, append) =
                if (dfa.finalStates contains t) {
                  (
                    dfa.q0,
                    word.toList.map(Some(_))
                  )
                } else {
                  val qStored = target.substring(0, q) + a
                  (
                    t,
                    qStored.substring(0, qStored.length - t).toList.map(Some(_))
                  )
                }
              val m = monoid.combine(
                appendWordTo(j, xs, List(Some(a))),
                appendWordTo(
                  i,
                  xs,
                  append
                )
              )
              (
                Cop1(r),
                m
              )
            }
        }
        edgesFromDfa ++ toNext
      }
      (notFromJ.toMap ++ jthComponent).toMap
    }
    val states = edges.map { case ((q, _), _) => q }.toSet + Cop2(i)
    val q0 = if (j == 0) Cop1(dfa.q0) else Cop2(0)
    val outF: Map[Q, Set[Concepts.Cupstar[X, B]]] =
      Map(
        Cop2(i) -> Set(xs.toList.sorted.foldRight[Concepts.Cupstar[X, B]](Nil) {
          case (x, acc) => List(Cop1(x), Cop2(None)) ++ acc
        })
      )
    new NSST(
      states,
      in.map(Some(_): Option[Char]) + None,
      xs,
      edges,
      q0,
      outF
    ).renamed
  }
  "Zhu's experiment case 2" should "be sat" in {
    val p = postfixDFA("aab", Set('a', 'b', 'c'))
    assert(p.accept("aaab".toList))
    assert(!p.accept("abab".toList))
    assert(!p.accept("ababaaba".toList))
    def toOptionList(s: String): List[Option[Char]] = s.toList.map(c => if (c == '#') None else Some(c))
    val aab = replaceAllNSST("aab", "b", 1, 0, "ab".toSet)
    assert(aab.transduce(toOptionList("aaab#")) == Set(toOptionList("aaab#ab#")))
    assert(aab.transduce(toOptionList("aaaa#")) == Set(toOptionList("aaaa#aaaa#")))
    assert(aab.transduce(toOptionList("aabaab#")) == Set(toOptionList("aabaab#bb#")))
    val aab31 = replaceAllNSST("aab", "b", 3, 1, "ab".toSet)
    assert(aab31.transduce(toOptionList("#aab##")) == Set(toOptionList("#aab##b#")))

    val in = "<sc>".toSet
    val sc10 = replaceAllNSST("<sc>", "", 1, 0, in)
    assert(sc10.transduce(toOptionList("<sc>#")) == Set(toOptionList("<sc>##")))
    assert(sc10.transduce(toOptionList("<sc#")) == Set(toOptionList("<sc#<sc#")))
    val sc = new NSST[Int, Option[Char], Option[Char], Int](
      Set.tabulate(7)(identity),
      in.map[Option[Char]](Some(_)) + None,
      Set(0, 1),
      {
        val monoid = Concepts.updateMonoid(Set(0, 1))
        val at0: NSST.Edges[Int, Option[Char], Int, Option[Char]] = Map.from{
          for (a <- in) yield (0, Some(a): Option[Char]) -> Set((0, appendWordTo(0, Set(0, 1), List(Some(a)))))
        }
        val others: NSST.Edges[Int, Option[Char], Int, Option[Char]] = List(
          ((0, None) -> Set((1, appendWordTo[Int, Option[Char]](0, Set(0, 1), Nil)))),
          ((1, Some('<')) -> Set((2, appendWordTo[Int, Option[Char]](1, Set(0, 1), List(Some('<')))))),
          ((2, Some('s')) -> Set((3, appendWordTo[Int, Option[Char]](1, Set(0, 1), List(Some('s')))))),
          ((3, Some('c')) -> Set((4, appendWordTo[Int, Option[Char]](1, Set(0, 1), List(Some('c')))))),
          ((4, Some('>')) -> Set((5, appendWordTo[Int, Option[Char]](1, Set(0, 1), List(Some('>')))))),
          ((5, None) -> Set((6, appendWordTo[Int, Option[Char]](0, Set(0, 1), Nil)))),
        ).toMap
        (at0 ++ others).toMap
      },
      0,
      Map(6 -> Set(List(Cop1(0), Cop2(None), Cop1(1), Cop2(None))))
    )
    assert(sc.transduce(toOptionList("#<sc>#")) == Set(toOptionList("#<sc>#")))
    assert(sc.transduce(toOptionList("#<sc#")) == Set())
    val start = System.nanoTime()
    val composed = NSST.composeNsstOfNssts(sc10, sc)
    info(s"elapsed:\t${(System.nanoTime() - start) / 1000000} ms")
    info(s"states:\t${composed.states.size}")
    info(s"variables:\t${composed.variables.size}")
    info(s"transition:\t${composed.edges.size}")
    assert(!composed.isEmpty)
    assert(composed.transduce(toOptionList("<sc<sc>>#")) == Set(toOptionList("<sc<sc>>#<sc>#")))
  }

  "Zhu's experiment case 3" should "be sat" in {
    val in = "a<sc>".toSet
    val sc20 = replaceAllNSST("<sc>", "a", 2, 0, in)
    val sc31 = replaceAllNSST("<sc>", "a", 3, 1, in)
  }
}
