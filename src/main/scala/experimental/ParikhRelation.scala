package com.github.kmn4.sst.experimental

import com.github.kmn4.sst.Presburger
import com.github.kmn4.sst.ParikhSST

// parikhAutomata の要素 Seq[Parikh...] を conjunction と呼ぶ
// 条件: conjunction は非空  (FIXME unique にする)
// TODO あるいは, unique だと思う Strategy とそうでないものとを用意して比較する
case class ParikhRelation[Q, A, L, I](
    parikhAutomata: Seq[Seq[ParikhAutomaton[Q, A, L, I]]],
    globalFormulas: GlobalFormulas[I]
) {
  type PA = ParikhAutomaton[Q, A, L, I]
  def maxID: Int = {
    require(parikhAutomata.nonEmpty)
    for {
      conjunction <- parikhAutomata.iterator
      pa <- conjunction.iterator
    } yield pa.id
  }.max

  // 入力: [((PA, ..., PA), phi)] -- 「右辺の変数が属すべき言語と大域整数制約の組」のリスト
  // 出力: this に入力を条件として課したときの PR
  // TODO eager にプロダクトをとることで，各変数の言語を単一に保つ
  def impose(preImages: Seq[(Seq[PA], GlobalFormulas[I])], rhs: Seq[Int]): ParikhRelation[Q, A, L, I] = {
    val rhsLangs = preImages
      .foldLeft(rhs.map(i => (i, Seq.empty[PA]))) {
        case (acc, (pas, _)) =>
          acc.lazyZip(pas).map { case ((i, ps), p) => (i, (ps :+ p)) }
      }
      .toMap
      .withDefaultValue(Seq.empty)
    ParikhRelation(
      parikhAutomata.zipWithIndex.map { case (pas, i)     => pas ++ rhsLangs(i) },
      globalFormulas ++ preImages.flatMap { case (_, phi) => phi }
    )
  }
}
