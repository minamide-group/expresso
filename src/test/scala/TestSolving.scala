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
    info(s"elapsed:\t${(System.nanoTime()-start)/1000000} ms")
    info(s"states:\t${t2.states.size}")
    info(s"variables:\t${t2.variables.size}")
    info(s"transition:\t${t2.edges.size}")
    assert(t2.transduce("aba#".toList) == Set("aba#bbb#abbba#".toList))
  }
}
