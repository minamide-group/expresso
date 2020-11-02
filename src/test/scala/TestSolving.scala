package com.github.kmn4.sst

import org.scalatest.flatspec._

class TestSolving extends AnyFlatSpec {
  import Solver.{replaceAllNSST, concatNSST, regexNSST, parikhNSST}
  def compositionRight[A, X](l: Seq[NSST[Int, A, A, Int]]): NSST[Int, A, A, Int] = l.reduceRight(_ compose _)
  def toOptionList(s: String): List[Option[Char]] = s.toList.map(c => if (c == '#') None else Some(c))
  def fromOptionList(l: List[Option[Char]]): String = l.map(_.getOrElse('#')).mkString
  def testTransduce[Q, X](
      sst: NSST[Q, Option[Char], Option[Char], X],
      w: String,
      expected: String*
  ) = assert(sst.transduce(toOptionList(w)) == expected.map(toOptionList).toSet)

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
  ) = NSST(
    states,
    in,
    xs,
    edges.map { case (q, a, r, m) => (q, a, updateOf(xs, m), r) }.toSet,
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
    val start = System.nanoTime()
    val t = s1 compose (s2 compose s3)
    info(s"elapsed:\t${(System.nanoTime() - start) / 1000000} ms")
    info(s"states:\t${t.states.size}")
    info(s"variables:\t${t.variables.size}")
    info(s"transition:\t${t.edges.size}")
    assert(t.transduce("aba#".toList) == Set("aba#bbb#abbba#".toList))
    info(s"witness: ${t.takeInput}")
    info(s"output: ${t.transduce(t.takeInput)}")
  }

  "Zhu's experiment case 2" should "be sat" in {
    // val p = postfixDFA("aab", Set('a', 'b', 'c'))
    // assert(p.accept("aaab".toList))
    // assert(!p.accept("abab".toList))
    // assert(!p.accept("ababaaba".toList))
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
    val exp = CatExp(CatExp(CatExp(CharExp('<'), CharExp('s')), CharExp('c')), CharExp('>'))
    val sc = regexNSST(2, 1, exp, in)
    assert(sc.transduce(toOptionList("#<sc>#")) == Set(toOptionList("#<sc>#")))
    assert(sc.transduce(toOptionList("#<sc#")) == Set())
    val start = System.nanoTime()
    val composed = sc10 compose sc
    info(s"elapsed:\t${(System.nanoTime() - start) / 1000000} ms")
    info(s"states:\t${composed.states.size}")
    info(s"variables:\t${composed.variables.size}")
    info(s"transition:\t${composed.edges.size}")
    assert(!composed.isEmpty)
    assert(composed.transduce(toOptionList("<sc<sc>>#")) == Set(toOptionList("<sc<sc>>#<sc>#")))
    info(s"witness: ${fromOptionList(composed.takeInput)}")
  }

  "Zhu's experiment case 3" should "be sat" in {
    val in = "a<sc>".toSet
    val sc20 = replaceAllNSST("<sc>", "a", 2, 0, in)
    testTransduce(sc20, "a<s#c>a#", "a<s#c>a#a<s#")
    val sc31 = replaceAllNSST("<sc>", "a", 3, 1, in)
    testTransduce(sc31, "a<s#c>a#a<s#", "a<s#c>a#a<s#c>a#")
    val concat23 = concatNSST(4, List(Right(2), Right(3)), in)
    testTransduce(concat23, "a<s#c>a#a<s#c>a#", "a<s#c>a#a<s#c>a#a<sc>a#")
    val re: RegExp[Char] = "a<sc>a".foldLeft[RegExp[Char]](EpsExp) {
      case (acc, c) => CatExp(acc, CharExp(c))
    }
    val reSST = regexNSST(5, 4, re, in)
    assert(reSST.transduce(toOptionList("####a<sc>a#")) == Set(toOptionList("####a<sc>a#")))
    assert(reSST.transduce(toOptionList("####a<sc>#")) == Set())
    testTransduce(reSST, "a<s#c>a#a<s#c>a#a<sc>a#", "a<s#c>a#a<s#c>a#a<sc>a#")
    val start = System.nanoTime()
    // sc20 -> sc31 -> concat -> reSST
    val composed = compositionRight(List(sc20, sc31, concat23, reSST))
    info(s"elapsed:\t${(System.nanoTime() - start) / 1000000} ms")
    info(s"states:\t${composed.states.size}")
    info(s"variables:\t${composed.variables.size}")
    info(s"transition:\t${composed.edges.size}")
    testTransduce(composed, "a<s#c>a#", "a<s#c>a#a<s#c>a#a<sc>a#")
    assert(!composed.isEmpty)
    val witness = composed.takeInput
    info(fromOptionList(witness))
    assert(composed.transduce(witness) != Set.empty)
  }

  "Zhu's experiment case 5" should "be unsat" in {
    val in = Set('a', 'b')
    def cat(n: Int) = concatNSST(n + 1, List(Right(n), Right(n)), in)
    val re1 = {
      val ab = CatExp(CharExp('a'), CharExp('b'))
      regexNSST(2, 1, CatExp(ab, StarExp(ab)), in)
    }
    def re(k: Int) = {
      val aa = CatExp(CharExp('a'), CharExp('a'))
      regexNSST(k + 1, k, CatExp(aa, StarExp(aa)), in)
    }
    def test(k: Int) = {
      val start = System.nanoTime()
      val composed = compositionRight((Seq(cat(0), re1) ++ (1 until k).map(cat) ++ Seq(re(k))))
      assert(composed.isEmpty)
      info(s"[k=$k]")
      info(s"elapsed:\t${(System.nanoTime() - start) / 1000000} ms")
      info(s"states:\t${composed.states.size}")
      info(s"variables:\t${composed.variables.size}")
      info(s"transition:\t${composed.edges.size}")
    }
    testTransduce(cat(1), "a#b#", "a#b#bb#")
    testTransduce(re1, "a#ab#", "a#ab#")
    testTransduce(re1, "a##")
    test(2)
    test(3)
    test(4)
    test(5)
  }

  "Variant of Zhu's benchmark int3" should "be sat" in {
    val alpha = "abc".toSet
    val s1 = replaceAllNSST("ab", "c", 1, 0, alpha)
    val s2 = replaceAllNSST("ac", "aaaa", 2, 1, alpha)
    val parikh = parikhNSST(3, alpha)
    val start = System.nanoTime()
    def elapsedMillis(): Long = (System.nanoTime() - start) / 1000000
    def printTime(s: String) = {
      info(s)
      info(s"elapsed:\t${elapsedMillis()} ms")
    }
    val composed = s1 compose s2
    printTime("composed")
    info(s"states: ${composed.states.size}")
    info(s"edges: ${composed.edges.size}")

    val parikhComposed = s1 compose (s2 compose parikh)
    printTime("prikhComposed")
    info(s"states:\t${parikhComposed.states.size}")
    info(s"edges:\t${parikhComposed.edges.size}")
    info(s"variables:\t${parikhComposed.variables.size}")

    assert(!composed.isEmpty)
    printTime("composed is not empty")

    val formula = parikhComposed.presburgerFormula
    printTime("Formula computed")

    import com.microsoft.z3
    val cfg = new java.util.HashMap[String, String]()
    cfg.put("model", "true")
    val ctx = new z3.Context(cfg)
    val freeVars = (0 until 3).map(i => s"y$i").map(y => y -> ctx.mkIntConst(y))
    val zero = ctx.mkInt(0)
    val positives = freeVars.map { case (_, v) => ctx.mkGe(v, zero) }
    val expr = Parikh.Formula.formulaToExpr(ctx, freeVars.toMap, formula)
    val growsOne = ctx.mkEq(ctx.mkSub(freeVars(2)._2, freeVars(0)._2), ctx.mkInt(1))
    val leThree = ctx.mkLe(freeVars(0)._2, ctx.mkInt(3))
    val solver = ctx.mkSolver()
    solver.add(expr +: leThree +: growsOne +: positives: _*)
    assert(solver.check() == z3.Status.SATISFIABLE)
    val m = solver.getModel()
    val witnessImage = ((0 until 3) zip freeVars).map {
      case (x, (_, i)) => x -> m.eval(i, false).toString.toInt
    }.toMap
    printTime("Z3 done")
    info(s"Image of witness:\t$witnessImage")

    val enft = NSST.convertNsstParikhNft(parikhComposed).toENFT
    printTime("Start to search for witness")
    val witness =
      enft.takeInputFor(witnessImage, m => m.exists { case (a, i) => i > witnessImage(a) })
    printTime("Got witness")
    info(s"witness: ${fromOptionList(witness)}") // => "aab#"
  }
}
