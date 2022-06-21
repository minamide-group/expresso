package com.github.kmn4.expresso.solver

import smtlib.Interpreter
import smtlib.interpreters.{CVC4Interpreter, Z3Interpreter}
import smtlib.lexer.Lexer
import smtlib.parser.Parser
import smtlib.trees.Commands._
import smtlib.trees.CommandsResponses._
import smtlib.trees.SimpleTreeTransformer
import smtlib.trees.Terms._
import java.io.StringReader
import scala.collection.mutable.{Map => MutMap}
import scala.util.control.Exception.nonFatalCatch

object DelegateSolver {

  case class TranspileError(msg: String) extends AnyVal
  case class ExecutionError(msg: String) extends AnyVal

  /** Abstraction for external tools (Z3, CVC4, etc.) */
  trait Delegate {
    case class TranspiledScript(script: Script)

    /** Transpile a new script from original `script`
      * so that it can be solved by the delegated program. */
    def transpile(script: Script): Either[TranspileError, TranspiledScript]

    /** Solve the transpiled script.
      * Right(Some) if SAT, Right(None) otherwise. Left if execution failed. */
    def solve(tscript: TranspiledScript): Either[ExecutionError, Option[Model]]
  }

  /** Delegate Interpreter to solve. */
  trait DelegateToInterpreter extends Delegate {
    def interpreter: Interpreter
    private def getModel(resp: SExpr) = {
      val defineFuns =
        resp match {
          case GetModelResponseSuccess(l) => l
          case sexp                       => throw new Exception(s"Failed to parse get-model response: ${sexp}")
        }
      val strModel = MutMap[String, String]()
      val intModel = MutMap[String, Int]()
      defineFuns.foreach {
        case DefineFun(FunDef(name, _, Sort(Identifier(SSymbol("String"), _), _), SString(v))) =>
          strModel += (name.name -> v)
        case DefineFun(FunDef(name, _, Sort(Identifier(SSymbol("Int"), _), _), SNumeral(v))) =>
          intModel += (name.name -> v.toInt)
        case sexp =>
          throw new Exception(s"Failed to parse model: ${sexp}")
      }
      Some(Model(strModel.toMap, intModel.toMap))
    }
    override def solve(tscript: TranspiledScript) = {
      val newValue = {
        tscript.script.commands.map(interpreter.eval).collect {
          case Error(msg) => throw new Exception(msg)
        }
        val checkSatResp = interpreter.eval(CheckSat());
        (checkSatResp: @unchecked) match {
          case CheckSatStatus(SatStatus) =>
            val getModelResp = interpreter.eval(GetModel())
            getModel(getModelResp)
          case CheckSatStatus(UnsatStatus)   => None
          case CheckSatStatus(UnknownStatus) => throw new Exception("Unknown satisfiability")
        }
      }
      nonFatalCatch.either(newValue).left.map(e => ExecutionError(e.getMessage))
    }
  }

  object Z3Delegate extends DelegateToInterpreter {
    override val interpreter = Z3Interpreter.buildDefault
    private val transFn = transform_countChar
    private val transformer = new SimplePreTermTransformer(transFn)
    override def transpile(script: Script) = {
      val cmds = script.commands.map(transformer.transform(_, ())._1)
      Right(TranspiledScript(Script(cmds)))
    }
  }

  object CVC5Delegate extends DelegateToInterpreter {
    override val interpreter =
      new CVC4Interpreter(
        "cvc5-macos",
        Array("-q", "-i", "--produce-models", "--strings-exp", "--lang", "smt2.6")
      )
    private val transFn =
      Seq(transform_countChar, renameFn("str.to.re", "str.to_re"), renameFn("str.in.re", "str.in_re"))
        .reduce(_ compose _)
    private val transformer = new SimplePreTermTransformer(transFn)
    override def transpile(script: Script) = {
      val cmds = script.commands.map(transformer.transform(_, ())._1)
      Right(TranspiledScript(Script(cmds)))
    }
  }

  // Transform utilities

  private def parseTerm(str: String): Term = {
    val lexer = new Lexer(new StringReader(str))
    val parser = new Parser(lexer)
    parser.parseTerm
  }

  private def renameFn: (String, String) => Term => Term = (from, to) => {
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(name), i), s), args) if name == from =>
      FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(to), i), s), args)
    case o => o
  }

  private def transform_countChar: Term => Term = {
    case FunctionApplication( // (str.count_char v s)
        QualifiedIdentifier(Identifier(SSymbol("str.count_char"), _), _),
        Seq(v, s: SString)
        ) =>
      parseTerm(s"""(- (str.len $v) (str.len (str.replace_all $v $s "")))""")
    case o => o
  }

  class SimplePreTermTransformer(transFn: Term => Term) extends SimpleTreeTransformer {
    override def pre(term: Term) = transFn(term)
    override def pre(sort: Sort) = sort
    override def post(term: Term) = term
    override def post(sort: Sort) = sort
  }
}
