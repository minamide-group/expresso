package com.github.kmn4.sst

import com.github.kmn4.sst.math.Presburger
import com.github.kmn4.sst.machine.ParikhSST
import com.github.kmn4.sst.language.Constraint.ParikhConstraint
import com.github.kmn4.sst.language.Constraint

/**
  * 制約を解くアルゴリズムを表現するクラス Strategy を提供する．
  *
  * 現在は卒論で用いたアルゴリズム ThesisStrategy と逆像計算に基づく PreImageStrategy
  * の 2 つを提供している．
  * TODO ThesisStrategy
  *
  * アルゴリズムの入力はペア
  *   (アルファベット, 文字列変数の集合，整数変数の集合，代入文の列，言語制約の集合，整数制約)．
  * より詳しく，
  *   - アルファベットは文字の集合
  *   - 文字列変数の集合は {0, 1, ..., n-1} で，具体的には n が与えられる
  *   - 整数変数の集合は文字列の有限集合で，この要素のみが結果のモデルに含まれる
  *   - 代入文は (左辺の文字列変数, PSST を構成するための構造, 右辺の文字列変数の列)
  *   - 言語制約は (文字列変数，PA を構成するための構造)
  *   - 整数制約は整数変数のみを含む線形算術論理式
  * を受け取る．
  *
  * 出力は充足可能かどうかの情報と，(sat ならば) 文字列変数と整数変数への値の割り当てとのペアである．
  */
package object strategy {
  case class Input(
      alphabet: Set[Char],
      stringVarNumber: Int,
      intVars: Set[String],
      assignments: Seq[Constraint.AtomicAssignment[Int]],
      assertions: Seq[Constraint.ParikhAssertion[Int]],
      arithFormulas: Seq[Presburger.Formula[String]]
  )
  type Models = (Seq[String], Map[String, Int])
  type Output = Option[Models]

  type Formulas[I, L] = Seq[Presburger.Formula[Either[I, L]]]
  type GlobalFormulas[I] = Seq[Presburger.Formula[I]]
  // PreImage は実際のところ LazyList
  type PreImage[Q, A, L, I] = Seq[(Seq[IdentifiedPA[Q, A, L, I]], GlobalFormulas[I])]
  type SolverPSST[C, I] = ParikhSST[Int, Option[C], Option[C], Int, Int, I]

}