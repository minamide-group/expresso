package com.github.kmn4.sst

import scala.util.Random.nextInt

import org.scalatest.funsuite._

class FunctionalnessTest extends AnyFunSuite {
  import Constraint._
  test("sstEndsWith meets spec") {
    val abc = "abc".toSet
    val ab = "ab".toSet
    val rev = Reverse().toSST(abc)
    val uf = UntilFirst("a").toSST(abc)
    val revE = rev.sstEndsWith(ab)
    val ufE = uf.sstEndsWith(ab)
    def endsWith(chars: Set[Char])(w: List[Char]): Set[List[Char]] = {
      for (i <- 0 until w.length if chars(w(i))) yield w.take(i + 1)
    }.toSet
    val endsWithAB = endsWith(ab) _
    for (i <- 0 until 100) {
      val cs = for (_ <- 0 until nextInt(10)) yield "abc" (nextInt(3))
      val w = cs.toList
      assert(rev.transduce(w).flatMap(endsWithAB) == revE.transduce(w))
      assert(uf.transduce(w).flatMap(endsWithAB) == ufE.transduce(w))
    }
    for (i <- 0 until 100) {
      val n = RandomTest.randomNsstCustomized()
      val e = n.sstEndsWith("a".toSet)
      for (j <- 0 until 10) {
        val cs = for (_ <- 0 until nextInt(10)) yield "ab" (nextInt(2))
        val w = cs.toList
        assert(n.transduce(w).flatMap(endsWith("a".toSet)) == e.transduce(w))
      }
    }
  }
  test("lengthCA counts length") {
    for (i <- 0 until 100) {
      val n = RandomTest.randomNsstCustomized()
      val ca = n.lengthCA
      for (i <- 0 until 100) {
        val cs = for (_ <- 0 until nextInt(10)) yield "ab" (nextInt(2))
        val w = cs.toList
        assert(n.transduce(w).map(_.length) == ca.transduce(w.map(Some.apply) :+ None))
      }
    }
  }
  test("isFunctional correctly decides functionalness for each solver SST") {
    val alpha = "ab".toSet
    assert(At(0).toSST(alpha).isFunctional)
    assert(At(1).toSST(alpha).isFunctional)
    assert(Insert(0, "hoge").toSST(alpha).isFunctional)
    assert(Insert(0, "").toSST(alpha).isFunctional)
    assert(Insert(1, "aa").toSST(alpha).isFunctional)
    assert(ReplaceAll("", "").toSST(alpha).isFunctional)
    assert(ReplaceAll("ab", "ba").toSST(alpha).isFunctional)
    assert(ReplaceAll("aa", "").toSST(alpha).isFunctional)
    assert(Reverse().toSST(alpha).isFunctional)
    assert(UntilFirst("").toSST(alpha).isFunctional)
    assert(UntilFirst("aa").toSST(alpha).isFunctional)
    assert(UntilFirst("ab").toSST(alpha).isFunctional)
    assert(!TakePrefix().toSST(alpha).isFunctional)
    assert(!TakeSuffix().toSST(alpha).isFunctional)
  }

  // Random test takes too long (sometimes more than 3 mins).
  // test("Random test for isFunctional (when functional only)") {
  //   import TestRandom._
  //   var c = 0
  //   for (_ <- 0 until 20) {
  //     val n = {
  //       val in = Set('a', 'b')
  //       val out = in
  //       val vars = Set('X', 'Y')
  //       val maxStates = 3
  //       val maxFNum = 2
  //       val maxRepeatB = 2
  //       val maxTransition = 2
  //       randomNSST(
  //         new NextState().nextState _,
  //         in,
  //         out,
  //         vars,
  //         maxStates,
  //         maxFNum,
  //         maxRepeatB,
  //         maxTransition
  //       )
  //     }
  //     if (n.isFunctional) {
  //       c += 1
  //       for (_ <- 0 until 100) {
  //         val w = nextAs("ab".toList, 5)
  //         assert(n.transduce(w).size <= 1)
  //       }
  //     }
  //   }
  //   info(s"$c cases were functional")
  // }

  test("isFunctional should terminates in reasonable time for composed solver SST") {
    val constraintBase = "./constraints"
    def compileFile(fname: String) = {
      import smtlib.trees.Commands.{Script, GetModel, CheckSat}
      import java.nio.file.FileSystems
      val path = FileSystems.getDefault().getPath(s"$constraintBase/$fname")
      val lexer = new smtlib.lexer.Lexer(new java.io.FileReader(path.toFile()))
      val parser = new smtlib.parser.Parser(lexer)
      val script = Script(parser.parseScript.commands.filter {
        case GetModel() => false
        case CheckSat() => false
        case _          => true
      })
      val solver = new Solver(())
      solver.executeTransPrint(script)

      val sl = solver.currentSL().getOrElse(???)
      val alphabet = {
        import Solver._
        val Constraint.SLConstraint(atoms, is, rs) = sl
        val contained =
          (atoms.map(usedAlphabetAtomic) ++ rs.map(_.re.usedAlphabet)).fold(Set.empty)(_ union _)
        val printable = ' ' to '~'
        contained ++ printable.find(c => !contained.contains(c))
      }
      Solver.compileConstraint(sl, alphabet)
    }
    assert(compileFile("deleteall.smt2")._1.isFunctional)
    // SST of replace_some_1 should be functional,
    // because it does not change length and y is unique for each length.
    assert(compileFile("nondet/replace_some_1.smt2")._1.isFunctional)
  }
}
