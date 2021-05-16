package com.github.kmn4.expresso.strategy

import com.github.kmn4.expresso.graphToMap
import com.github.kmn4.expresso.machine.ParikhAutomaton
import com.github.kmn4.expresso.machine.ParikhSST
import com.github.kmn4.expresso.math.Presburger

// A*(#1)...(#k-1)A*, n1, ..., nl -> A*
private trait Transduction[A, B] {
  // pa の逆像を計算する
  // maxID がいまある最大の ID．
  // 新しく使う ID はこれよりも大きくする．
  def preImage[R, K](pa: IdentifiedPA[R, B, K, String], maxID: Int): PreImage[Int, A, Int, String]
}

private object Transduction {
  // psst の定義域は w_0 #_0 ... #_n-2 w_n-1 の形をした文字列の集合
  implicit class ParikhTransduction[Q, A, B, X, L](
      psst: ParikhSST[Q, Either[A, Int], B, X, L, String]
  ) extends Transduction[A, B] {

    // psst の定義域が w_0 #_0 ... #_n-2 w_n-1 のとき arity = n
    val arity = psst.inSet.flatMap(_.toOption).maxOption.getOrElse(-1) + 2

    override def preImage[R, K](
        ipa: IdentifiedPA[R, B, K, String],
        maxID: Int
    ): PreImage[Int, A, Int, String] = {
      val IdentifiedPA(id, lang) = ipa
      // lang を PSST とみなす
      // PSST 同士の合成をする (LC-APSST まで)
      // 受理状態を固定するごとに1つの PA をつくる
      // PA を # で分割して PR にする

      // lang を PSST とみなす
      val langPST = {
        // TODO PairkhAutomaton のメソッドを使う
        ParikhSST[R, B, Nothing, Nothing, K, String](
          lang.states,
          lang.inSet,
          Set.empty,
          lang.ls,
          lang.is,
          lang.edges.map { case (q, b, v, r) => (q, b, Map.empty, v, r) },
          lang.q0,
          lang.acceptRelation.map { case (qf, v) => (qf, Nil, v) },
          lang.acceptFormulas
        )
      }

      // PSST 同士の合成をする (LC-PA まで)
      val lcp = psst
        .composeNsstsToMsst[R, Nothing, Nothing, K](psst, langPST)
        .toLocallyConstrainedAffineParikhSST
        .toLocallyConstrainedParikhSST
        .renamed
        .optimized

      // lcp を受理状態ごとに PA へ分割
      // NOTE 分割しないと遅くなる場合がある．
      //      例えば 'group_sc' では 2 倍の差がある．
      val pas: Iterator[ParikhAutomaton[Int, Either[A, Int], Int, String]] = {
        val qf = lcp.states.maxOption.getOrElse(0) + 1 // 存在しなかったら Iterator が空
        val states = lcp.states + qf
        val lastSharp = Right(arity - 1)
        val zero = lcp.ls.map(_ -> 0).toMap
        // TODO 到達性で状態を減らす
        // TODO 不要な L を削除
        lcp.outGraph.iterator.map {
          case (q, _, v, phi) =>
            ParikhAutomaton(
              states,
              lcp.inSet + lastSharp,
              lcp.ls,
              lcp.is,
              lcp.edges.map { case (q, a, _, v, r) => (q, a, v, r) } + ((q, lastSharp, v, qf)),
              lcp.q0,
              Set((qf, zero)),
              lcp.globalAcceptFormulas :+ phi // TODO phi は Seq のほうがいいかも?
            )
        }
      }

      def copyVar[L](paID: Int, l: L) = s"copy_${paID}_${l}"
      def sumVar[L](paID: Int, l: L) = s"sum_${paID}_${l}"

      def split[Q, L](
          pa: ParikhAutomaton[Q, Either[A, Int], L, String]
      ): Iterator[(Seq[IdentifiedPA[Q, A, L, String]], Seq[Presburger.Formula[String]])] = {
        type Edge = (Q, Either[A, Int], Map[L, Int], Q)

        // cache
        val backTrans: Map[(Q, Either[A, Int]), Set[(Q, Map[L, Int])]] =
          graphToMap(pa.edges) { case (q, a, v, r) => (r, a) -> (q, v) }
        val trans: Map[(Q, Either[A, Int]), Set[(Q, Map[L, Int])]] =
          graphToMap(pa.edges) { case (q, a, v, r) => (q, a) -> (r, v) }

        // pa 上で qf から戻れないものを刈る
        def pruneStatesBack(qf: Q): (Set[Q], Set[Edge]) =
          com.github.kmn4.expresso.searchStates(Set(qf), pa.inSet) {
            case (r, a) => backTrans((r, a))
          }(_._1, { case (r, a, (q, v)) => (q, a, v, r) })

        // pa 上で q0 から到達できないものを刈る
        def pruneStatesForward(q0: Q): (Set[Q], Set[Edge]) =
          com.github.kmn4.expresso.searchStates(Set(q0), pa.inSet) {
            case (q, a) => trans((q, a))
          }(_._1, { case (q, a, (r, v)) => (q, a, v, r) })

        // pa 上で q0 から到達可能かつ qf から逆到達可能
        def pruneStates(q0: Q, qf: Q): (Set[Q], Set[Edge]) = {
          val (qs1, es1) = pruneStatesBack(qf)
          val (qs2, es2) = pruneStatesForward(q0)
          (qs1 intersect qs2, es1 intersect es2)
        }

        // pa の状態を qs, 辺集合を es に制限．
        // 状態が空なら None になる
        // NOTE acceptRelation は呼び出し元で上書きすること
        def statesRemoved(qs: Set[Q], es: Set[Edge]): Option[ParikhAutomaton[Q, Either[A, Int], L, String]] =
          if (qs.isEmpty) None
          else Some { pa.copy(states = qs, edges = es) }

        def prune(q0: Q, qf: Q): Option[ParikhAutomaton[Q, Either[A, Int], L, String]] = {
          val (qs, es) = pruneStates(q0, qf)
          statesRemoved(qs, es)
        }

        def pruneBackward(qf: Q): Option[ParikhAutomaton[Q, Either[A, Int], L, String]] = {
          val (qs, es) = pruneStatesBack(qf)
          statesRemoved(qs, es)
        }

        // sharp はないはず．あったら例外を投げる
        def mustRemoveSharps(
            pa: ParikhAutomaton[Q, Either[A, Int], L, String]
        ): ParikhAutomaton[Q, A, L, String] = {
          pa.copy(
            inSet = pa.inSet.flatMap(_.left.toOption),
            edges = pa.edges.map(e => e.copy(_2 = e._2.left.toOption.get))
          )
        }

        def splitAux(
            pa: ParikhAutomaton[Q, Either[A, Int], L, String],
            i: Int
        ): Iterator[(Seq[IdentifiedPA[Q, A, L, String]], Seq[Presburger.Formula[String]])] = {
          val sharpEdge: Map[Int, Iterable[Edge]] = graphToMap(pa.edges.filter(_._2.isRight)) {
            case e @ (_, Right(i), _, _) => i -> e
            case _                       => throw new Exception("This cannot be the case.")
          }

          val newID = maxID + i + 1

          if (i == 0) {
            for {
              sharp0 @ (q0, _, v, _) <- sharpEdge(0).iterator
              pa0 <- pruneBackward(q0).map { pa => pa.copy(acceptRelation = Set((q0, v))) }
            } yield {
              import Presburger._
              val noSharp = mustRemoveSharps(pa0)
              val syncFormulas = // PA と大域整数制約の同期
                pa0.ls.toSeq.map(l => Eq[Either[String, L]](Var(Right(l)), Var(Left(sumVar(newID, l)))))
              val newPA = noSharp.copy(acceptFormulas = syncFormulas)
              val ipa = IdentifiedPA(newID, newPA)
              (Seq(ipa), Seq.empty)
            }
          } else if (i > 0) {
            for {
              sharp1 @ (q1, _, _, r1) <- sharpEdge(i - 1).iterator
              sharpI @ (qi, _, v, _) <- sharpEdge(i)
              paI <- prune(r1, qi).map { pa => pa.copy(q0 = r1, acceptRelation = Set((qi, v))) }.toList
              pa1 <- pruneBackward(q1).map { pa =>
                // 再帰のため最後に #_i-1 で遷移するようにしたい
                // TODO もう少し綺麗に書けるのでは
                //      例えば PA は # 終端しない文字列組を受理することにする
                pa.copy(states = pa.states + r1, edges = pa.edges + sharp1)
              }.toList
              (relation1, formula) <- splitAux(pa1, i - 1)
            } yield {
              import Presburger._
              val noSharp = mustRemoveSharps(paI)
              // l (L) === copy_id_l (I)
              val copyFormulas =
                paI.ls.toSeq.map(l => Eq[Either[String, L]](Var(Right(l)), Var(Left(copyVar(newID, l)))))
              // sum_id_l === sum_{id-1}_l + copy_id_l
              val syncFormulas = paI.ls.map { l =>
                val sumL = Var(sumVar(newID, l))
                val prevL = Var(sumVar(newID - 1, l))
                val copyL = Var(copyVar(newID, l))
                Eq(sumL, Add(Seq(prevL, copyL)))
              }
              val newPA = noSharp.copy(acceptFormulas = copyFormulas)
              val ipa = IdentifiedPA(newID, newPA)
              (relation1 :+ ipa, formula ++ syncFormulas)
            }
          } else throw new Exception("i < 0")
        }

        splitAux(pa, arity - 1)
      }

      for {
        pa <- pas
        (rel, phi) <- split(pa)
      } yield {
        val paPhis = pa.acceptFormulas
          .map(_.renameVars {
            case Right(l) => sumVar(maxID + arity, l)
            case Left(i)  => i
          })
        val wrapped = rel.map(Seq(_))
        val formula = phi ++ paPhis
        ParikhRelation(wrapped, formula)
      }
    }

  }

}
