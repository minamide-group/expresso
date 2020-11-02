package com.github.kmn4.sst.smtlib2

import scala.collection.immutable.ArraySeq

class Parser(input: String) {
  sealed trait Token
  case object EOF extends Token
  case object LParen extends Token
  case object RParen extends Token
  case class StringLiteral(s: String) extends Token
  case class IntLiteral(i: Int) extends Token
  case class SymbolToken(name: String) extends Token
  val tokenIter: Iterator[Token] = new Iterator[Token] {
    private val eof = raw"".r
    private val lpar = raw"(?s)(\().*".r
    private val rpar = raw"(?s)(\)).*".r
    private val slit = raw"""(?s)("[^"]*").*""".r
    // private val ilit = raw"(?:(0)(?![^0-9])|([1-9][0-9]*)).*".r
    private val ilit = raw"(?s)(\d+).*".r
    private val sym = """(?s)([\S&&[^;"\(\)]][\S&&[^;"\(\)]]*).*""".r
    private val skip = raw"(?s)((?:\s*;[^\n]*\n)*\s*).*".r // comments and spaces
    private var buffer = input match {
      case skip(s) => input.drop(s.length)
      case _ => input
    }
    def removeSkip() = buffer match {
      case skip(s) => buffer = buffer.drop(s.length)
      case _ => ()
    }
    def hasNext: Boolean = true
    def next(): Token = {
      val (token, s) = buffer match {
        case eof() => (EOF, "")
        case lpar(s) => (LParen, s)
        case rpar(s) => (RParen, s)
        case slit(s) => (StringLiteral(s.drop(1).dropRight(1)), s)
        case ilit(s) => (IntLiteral(s.toInt), s)
        case sym(s) => (SymbolToken(s), s)
        case skip => throw new Exception("Failed to tokenize")
      }
      buffer = buffer.drop(s.length)
      removeSkip()
      token
    }
  }
  var token = tokenIter.next()
  def advance() = {
    token = tokenIter.next()
  }
  def eat(t: Token) =
    if (t == token) advance()
    else throw new Exception(s"Parse error: expected $t but $token found.")

  def parseList(): Seq[SExpr] = {
    var res: Seq[SExpr] = ArraySeq.empty
    while (token != RParen) {
      res :+= parseSExpr()
    }
    res
  }

  def parseSExpr(): SExpr = token match {
    case StringLiteral(s) =>
      advance()
      StringConst(s)
    case IntLiteral(i) =>
      advance()
      NumConst(i)
    case SymbolToken(name) =>
      advance()
      Symbol(name)
    case LParen =>
      advance()
      val ss = parseList()
      eat(RParen)
      Call(ss: _*)
    case RParen => throw new Exception("Parse error: expected S-exp but RParen found.")
    case EOF => throw new Exception("Parse error: expected S-exp but EOF found.")
  }

  def parse(): Seq[SExpr] = {
    var res: Seq[SExpr] = ArraySeq.empty
    while (token != EOF) {
      res :+= parseSExpr()
    }
    res
  }
}

object Parser {
  def parse(input: String): Seq[SExpr] = new Parser(input).parse()
}
