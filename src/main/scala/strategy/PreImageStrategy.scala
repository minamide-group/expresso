package com.github.kmn4.sst.strategy

import com.microsoft.z3
import com.github.kmn4.sst._
import com.github.kmn4.sst.math._
import com.github.kmn4.sst.machine._
import com.github.kmn4.sst.language.Constraint._
import com.typesafe.scalalogging.Logger

/**
  * 逆像計算に基づくアルゴリズム．
  * TODO intVars に含まれるもののみを返すようにする
  */
class PreImageStrategy(logger: Logger) extends Strategy {
  // pr の satisfialibity を確認
  // sat なら x_0, x_1, ... の値と i_0, i_1, ... の値を返す
  // 等式の左辺に現れる変数の値は返さないことに注意
  private def checkClause(pr: SolverPR[Char, String]): Option[(Seq[String], Map[String, Int])] = {
    // 共通部分をとる
    // 異なる文字列変数に対応する PA のログ変数がかぶらないようにする
    val psts: Seq[ParikhSST[Int, Char, Char, Unit, (Int /* index */, Int /* l */ ), String]] =
      pr.parikhAutomata.zipWithIndex.map {
        case (pas, idx) =>
          val pa = pas.map(_.pa).reduce[ParikhAutomaton[Int, Char, Int, String]] {
            case (p, q) => p.intersect(q).renamed
          }
          pa.toParikhSST.renamed(identity _, identity _, l => (idx, l))
      }
    // 整数変数 int_*, ログ変数 log_*_*, 束縛変数 bound_*
    val pstFormulas = psts.flatMap { pst =>
      val accept = pst.acceptFormula.renameVars {
        case Left(i)         => s"int_$i"
        case Right((idx, l)) => s"log_${idx}_$l"
      }
      val parikh = pst.parikhImageFormula.renameVars {
        case Left(b)         => s"bound_$b"
        case Right((idx, l)) => s"log_${idx}_$l"
      }
      Seq(accept, parikh)
    }
    val globalFormulas = pr.globalFormulas.map(_.renameVars(i => s"int_$i"))
    val formula = Presburger.Conj(pstFormulas ++ globalFormulas)
    withZ3Context { (ctx) =>
      val solver = ctx.mkSolver()
      val z3Expr = Presburger.Formula.formulaToZ3Expr(ctx, Map.empty[String, z3.IntExpr], formula)
      solver.add(z3Expr)
      if (solver.check() == z3.Status.SATISFIABLE) {
        val model = solver.getModel()
        def getValue(name: String): Int = model.eval(ctx.mkIntConst(name), false).toString().toInt
        // 得られたモデルの値を出力する入力文字列を探す
        val inputs = psts.map { pst =>
          val v = pst.ls.map { case il @ (idx, l) => il -> getValue(s"log_${idx}_$l") }.toMap
          pst.inputOutputFor(v)._1.mkString
        }
        // 整数変数のモデル
        val pat = "^int_(.*)".r
        val intVarValues = formula.freeVars.collect {
          case i @ pat(name) => name -> getValue(i)
        }
        Some((inputs, intVarValues.toMap))
      } else None
    }
  }
  // TODO これは Solver 側
  def parseIntModel(iv: Map[String, Int]): Map[String, Int] =
    iv.collect { case (name, value) if name.indexOf("user_") == 0 => name.drop(5) -> value }
  private var models: Output = None
  override def checkSat(constraint: Input): Boolean = {
    val config = organize(constraint)
    val relGen = iteratePreImage(config)
    models = {
      val iter = for {
        rel <- relGen
        models <- checkClause(rel)
      } yield models
      iter.nextOption()
    }
    models.nonEmpty
  }
  override def getModel(): Output = models

  private type PST = ParikhSST[Int, Either[Char, Int], Char, Int, Int, String]
  private type SolverPR[C, I] = ParikhRelation[Int, C, Int, I]

  private def assingmentToPSST[S](assignment: AtomicAssignment[S], alphabet: Set[Char]): PST =
    assignment match {
      case ParikhAssignment(_, trans, _) => {
        val psst = trans.toParikhSST(alphabet)
        psst.copy(
          inSet = psst.inSet.map(Left.apply),
          edges = psst.edges.map(e => e.copy(_2 = Left(e._2)))
        )
      }
      case CatAssignment(_, wordAndVars) => {
        // TODO wordsAndVars が少なくとも1つの文字列変数を含むことを仮定している点を緩和
        type Q = Int
        type A = Either[Char, Int]
        type B = Char
        type X = Unit
        type E = NSST.Edge[Q, A, B, X]
        type O = NSST.Out[Q, X, B]
        val depSize: Int = assignment.dependeeVars.size
        val states: Set[Q] = (0 until depSize).toSet
        val inSet: Set[A] = alphabet.map(Left.apply) ++ (0 to depSize - 2).map(Right.apply).toSet
        // w0 x0 w1 ... wn-1 xn-1 wn のときの w0 ... wn
        val words: Seq[Seq[Char]] = {
          wordAndVars.foldRight(List(Seq.empty[B])) {
            case (Left(s), h :: rst) => (s ++ h) :: rst
            case (Right(_), acc)     => Nil :: acc
            case _                   => throw new Exception("This cannot be the case")
          }
        }
        val edges: Set[E] = {
          val loop: Iterable[E] =
            for {
              i <- 0 to depSize - 1
              a <- alphabet
            } yield {
              val adding = List(Cop1(()), Cop2(a))
              val m = Map(() -> adding)
              (i, Left(a), m, i)
            }
          val next: Iterable[E] =
            (0 to depSize - 2).map { i =>
              val xbs = Cop1(()) :: words(i + 1).map(Cop2.apply).toList
              val m = Map(() -> xbs)
              (i, Right(i), m, i + 1)
            }
          (loop ++ next).toSet
        }
        val outGraph: Set[O] = {
          val added: Cupstar[X, B] =
            (words(0).map(Cop2.apply) ++ Seq(Cop1(())) ++ words.last.map(Cop2.apply)).toList
          Set((depSize - 1, added))
        }
        NSST(
          states,
          inSet,
          Set(()),
          edges,
          0,
          graphToMap(outGraph)(identity)
        ).renamed.toParikhSST
      }
    }

  private implicit class AssignmentToPSST[S](assignment: AtomicAssignment[S]) {
    def toExpPST(alphabet: Set[Char]): PST = assingmentToPSST(assignment, alphabet)
  }

  private case class PreImagable(pst: PST, rhs: Seq[Int])

  // 条件: transductions は lhs について昇順
  // 条件: relation の PA は lhs について昇順で，0 から順にならぶ
  private case class Configuration(
      transductions: Seq[PreImagable],
      relation: ParikhRelation[Int, Char, Int, String]
  )

  // トランスダクション，言語，整数制約を PST と PR にまとめる
  // NOTE assignments は左辺変数でソート済みと仮定
  private def organize(constraint: Input): Configuration = {
    // val Triple(assignments, assertions, _) = triple
    val maxVar = constraint.stringVarNumber - 1
    val alphabet = constraint.alphabet
    // assignments から PST を構成
    val transes = constraint.assignments.map { a => PreImagable(a.toExpPST(alphabet), a.dependeeVars) }
    // assertions と arithFormulas から PR が得られる
    val rel = {
      val paMap = constraint.assertions.groupMap(_.stringVar)(_.lang.toParikhAutomaton(alphabet))
      val pas = (0 to maxVar).map { idx =>
        val all = ParikhAutomaton.universal[Int, Char, Int, String](0, alphabet)
        paMap.getOrElse(idx, Seq.empty).foldLeft(all) {
          case (acc, pa) => acc.intersect(pa).renamed
        }
      }
      val withID = pas.zipWithIndex.map { case (pa, idx) => Seq(IdentifiedPA(idx, pa)) }
      ParikhRelation(withID, constraint.arithFormulas)
    }
    Configuration(transes, rel)
  }

  // transductions が非空である間 relation の逆像を計算する
  // disjunction が現れると非決定的な選択をする．この非決定性は Iterator が表している．
  private def iteratePreImage(config: Configuration): Iterator[ParikhRelation[Int, Char, Int, String]] = {
    import Transduction._
    val Configuration(ts, rel) = config
    ts.foldRight(LazyList(rel)) {
        case (PreImagable(pst, rhs), acc) =>
          type PA = IdentifiedPA[Int, Char, Int, String]
          // next() すると pst^-1(lang) から1つずつ選んだ組を返す
          // TODO PR において各変数の言語が単一の PA で表されればにここは不要になる
          def clauseChoices(
              langs: LazyList[PA],
              maxID: Int
          ): Iterator[Seq[(Seq[PA], GlobalFormulas[String])]] = {
            val idInc = rhs.length // maxID は逆像をとるたび idInc 分だけ増える
            var mxid = maxID - idInc
            choose(
              langs.map { lang =>
                mxid += idInc
                new Transduction.ParikhTransduction(pst).preImage(lang, mxid)
              }
            ).iterator
          }
          for {
            rel <- acc
            choice <- {
              val lhs = rel.parikhAutomata.length - 1
              val automata = LazyList.from(rel.parikhAutomata(lhs))
              clauseChoices(automata, rel.maxID)
            }
          } yield {
            // 1. rel から最右要素を除く
            // 2. rel へ rhs に従って choice を追加する
            ParikhRelation.impose(
              rel.copy(parikhAutomata = rel.parikhAutomata.dropRight(1)),
              choice,
              rhs
            )
          }
      }
      .iterator
  }

}
