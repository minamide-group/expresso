package com.github.kmn4.sst.strategy

import com.github.kmn4.sst.math.Presburger
import com.github.kmn4.sst.machine.ParikhSST

// parikhAutomata の要素 Seq[Parikh...] を conjunction と呼ぶ
// 条件: conjunction は非空  (TODO unique にする)
// TODO あるいは, unique だと思う Strategy とそうでないものとを用意して比較する
case class ParikhRelation[Q, A, L, I](
    parikhAutomata: Seq[Seq[IdentifiedPA[Q, A, L, I]]],
    globalFormulas: GlobalFormulas[I]
) {
  def maxID: Int = {
    require(parikhAutomata.nonEmpty)
    for {
      conjunction <- parikhAutomata.iterator
      pa <- conjunction.iterator
    } yield pa.id
  }.max

  // 重複する id がないことを assert
  def assertNoDuplicate: Unit = {
    val pas = parikhAutomata.flatten.map(_.id)
    val distinct = pas.distinct
    assert(distinct.length == pas.length)
  }
}

object ParikhRelation {
  type PA[A, I] = IdentifiedPA[Int, A, Int, I]

  // 入力: [((PA, ..., PA), phi)] -- 「右辺の変数が属すべき言語と大域整数制約の組」のリスト
  // 出力: this に入力を条件として課したときの PR
  def impose[A, I](
      rel: ParikhRelation[Int, A, Int, I],
      preImages: Seq[(Seq[PA[A, I]], GlobalFormulas[I])],
      rhs: Seq[Int]
  ): ParikhRelation[Int, A, Int, I] = {
    val rhsLangs = preImages
      .foldLeft(rhs.map(i => (i, Seq.empty[PA[A, I]]))) {
        case (acc, (pas, _)) =>
          acc.lazyZip(pas).map { case ((i, ps), p) => (i, (ps :+ p)) }
      }
      .toMap
      .withDefaultValue(Seq.empty)
    ParikhRelation(
      rel.parikhAutomata.zipWithIndex.map {
        case (pas, i) =>
          assert(pas.length == 1)
          val IdentifiedPA(id, pa) = pas.head
          val intersection = rhsLangs(i).map(_.pa).fold(pa) { case (p, q) => (p intersect q).renamed }
          Seq(IdentifiedPA(id, intersection))
      },
      rel.globalFormulas ++ preImages.flatMap { case (_, phi) => phi }
    )
  }

}
