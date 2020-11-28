package com.github.kmn4.sst

import org.scalatest.funsuite._
import com.github.kmn4.sst.Replacer._
import com.github.kmn4.sst.Replacer.PCRE._

class TestReplacer extends AnyFunSuite {
  def empty: PCRE[Char, String] = Empty()
  def eps: PCRE[Char, String] = Eps()
  implicit def chars(s: String): PCRE[Char, String] = Chars(s.toSet)
  def cat(es: PCRE[Char, String]*): PCRE[Char, String] = es.fold(eps)(Cat.apply[Char, String])
  def alt(e1: PCRE[Char, String], e2: PCRE[Char, String]): PCRE[Char, String] = Alt(e1, e2)
  def greedy(e: PCRE[Char, String]): PCRE[Char, String] = Greedy(e)
  def nonGreedy(e: PCRE[Char, String]): PCRE[Char, String] = NonGreedy(e)
  def group(e: PCRE[Char, String], x: String): PCRE[Char, String] = Group(e, x)
  def gderiv(e: PCRE[Char, String], x: String): PCRE[Char, String] = GDeriv(e, x)

  def firstMatch[A, X](e: PCRE[A, X]): PCRE[A, X] =
    PCRE.Cat(PCRE.Cat(PCRE.NonGreedy(PCRE.Chars(e.usedChars)), e), PCRE.Greedy(PCRE.Chars(e.usedChars)))

  def repetitiveMatch[A, X](e: PCRE[A, X]): PCRE[A, X] = PCRE.Greedy(PCRE.Alt(e, PCRE.Chars(e.usedChars)))

  def prettyParsedChar(c: ParsedChar[Char, String]): String = c match {
    case Left(a)        => a.toString()
    case Right(LPar(x)) => s"(<$x>"
    case Right(RPar(x)) => s")<$x>"
  }
  def prettyParsed(w: Parsed[Char, String]): String = w.map(prettyParsedChar).mkString

  def exec(e: PCRE[Char, String], w: Seq[Char]) = {
    val p = e.toParser
    val parsedSet = p.transduce(w).map(prettyParsed)
    assert(parsedSet.size <= 1)
    val parseResult = parsedSet.headOption.map(w => s"""\"$w\"""").getOrElse("No match")
    info(s"""\"$w\" => $parseResult""")
  }

  def execAll(e: PCRE[Char, String])(cases: Seq[Char]*) = test(s"$e") {
    cases.foreach(w => exec(e, w))
  }

  execAll(greedy(alt(group(cat("a", greedy(alt("b", "c"))), "x"), "abc")))("babcaaccca", "")
  execAll(greedy(group(alt("a", eps), "x")))("aaa", "")
  execAll(group(cat(greedy("a"), group(greedy("b"), "y")), "x"))("aaabba", "", "bb")
  execAll(firstMatch(group(cat(greedy("a"), group(greedy("b"), "y")), "x")))("aaabba", "", "bb")
  execAll(repetitiveMatch(group(cat(greedy("a"), group(greedy("b"), "y")), "x")))("aaabba", "", "bb")

  test("replace") {
    val s = replaceAllSST(
      cat("a", greedy(alt("b", "c"))),
      Replacement[Char, String](Seq(Left('a'), Right(None), Left('a')))
    )
    assert(s.transduce("abc") == Set("aabca".toList))
    assert(s.transduce("abca") == Set("aabcaaaa".toList))
  }
}
