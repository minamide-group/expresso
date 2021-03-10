package com.github.kmn4.sst

import org.scalatest.funsuite._

import com.github.kmn4.sst.language.Replacer.PCRE._
import com.github.kmn4.sst.language.Replacer._

class ReplacerTest extends AnyFunSuite {
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

  // Set of alphabet used in all of tests in this class.
  val alphabet = "abc".toSet

  def exec(e: PCRE[Char, String], w: Seq[Char]) = {
    val p = e.toParser(alphabet)
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

  def testReplaceAll(e: PCRE[Char, String], replacement: Replacement[Char, String])(
      cases: (Seq[Char], Seq[Char])*
  ) = test(s"Replace all $e with $replacement") {
    val s = Compiler.replaceAllSST(e, replacement, alphabet)
    for ((w, expected) <- cases) {
      val got = s.transduce(w)
      assert(got.size == 1)
      assert(got.head == expected)
    }
  }

  def replacement(w: Any*): Replacement[Char, String] = Replacement(
    w.collect {
      case c: Char   => Left(c)
      case s: String => Right(Some(s))
      case 0         => Right(None)
    }
  )

  testReplaceAll(cat("a", greedy(alt("b", "c"))), replacement('a', 0, 'a'))(
    ("abc", "aabca"),
    ("abca", "aabcaaaa")
  )

  testReplaceAll(
    cat(group(greedy("a"), "x"), group(greedy("b"), "y"), group(greedy("c"), "z")),
    replacement("z", "y", "x")
  )(("aabbcc", "ccbbaa"), ("bbc", "cbb"), ("bab", "bba"))

  testReplaceAll(greedy("ab"), replacement(0, 0, 0))(("ab", "ababab"), ("", ""), ("b", "bbb"))

  testReplaceAll(
    group(cat(group(greedy("a"), "x"), group(greedy("b"), "y")), "z"),
    replacement("x", "y", "z")
  )(
    ("ab", "abab"),
    ("ba", "bbaa"),
    ("", "")
  )

  testReplaceAll(greedy("a"), replacement('(', 0, ')'))(("", "()"), ("a", "(a)()"))

  // Bugs (nullable regexes that put higher precedence on the empty string)
  // testReplaceAll(eps, replacement('(', 0, ')'))(("a", "()a()"))
  // testReplaceAll(alt(eps, "a"), replacement('(', 0, ')'))(("", "()"), ("a", "()(a)()"))
  // testReplaceAll(nonGreedy("a"), replacement('(', 0, ')'))(("", "()"), ("a", "()(a)()"))
  // testReplaceAll(
  //   cat(group(greedy("a"), "x"), group(nonGreedy("b"), "y")),
  //   replacement('(', "y", "x", ')')
  // )(("ab", "(a)()(b)()"))
}
