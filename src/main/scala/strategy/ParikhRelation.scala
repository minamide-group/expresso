package com.github.kmn4.expresso.strategy

import com.github.kmn4.expresso.machine.ParikhAutomaton

// parikhAutomata の要素 Seq[Parikh...] を conjunction と呼ぶ．
// 条件: conjunction は非空
// TODO 現在，各 conjunction はシングルトンなもののみ考えている．
//      そうでない Strategy を用意して比較する
private case class ParikhRelation[Q, A, L, I](
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

  def lazyIntersect(that: ParikhRelation[Q, A, L, I]): ParikhRelation[Q, A, L, I] = {
    val zip = parikhAutomata.zipAll(that.parikhAutomata, Seq.empty, Seq.empty)
    val pas = zip.map { case (xs, ys) => xs ++ ys }
    val phis = globalFormulas ++ that.globalFormulas
    ParikhRelation(pas, phis)
  }

}

private object ParikhRelation {
  type PA[A, I] = IdentifiedPA[Int, A, Int, I]

  def eagerIntersect[A, I](rel: ParikhRelation[Int, A, Int, I]): ParikhRelation[Int, A, Int, I] = {
    rel.parikhAutomata.indices.foldLeft(rel) { case (acc, idx) => ParikhRelation.eagerIntersect(acc, idx) }
  }

  def eagerIntersect[A, I](rel: ParikhRelation[Int, A, Int, I], idx: Int): ParikhRelation[Int, A, Int, I] = {
    def intersect(pas: Seq[IdentifiedPA[Int, A, Int, I]]) = pas.headOption map { hd =>
      val pa = pas.tail.foldLeft(hd.pa) { case (acc, p) => acc.intersect(p.pa).renamed }
      IdentifiedPA(rel.maxID + 1, pa)
    }
    val automata = rel.parikhAutomata.updated(idx, intersect(rel.parikhAutomata(idx)).toSeq)
    rel.copy(parikhAutomata = automata)
  }

  def impose[A, I](
      rel: ParikhRelation[Int, A, Int, I],
      preImages: ParikhRelation[Int, A, Int, I], // 右辺変数に新しく追加される制約
      rhs: Seq[Int] // 右辺変数のリスト
  ): ParikhRelation[Int, A, Int, I] = {
    // require(rel.parikhAutomata.forall(_.size == 1))
    val ParikhRelation(pas, phi) = preImages
    val rhsPas = rhs zip preImages.parikhAutomata
    val rhsPa = for {
      (rh, pas) <- rhsPas
      pa <- pas
    } yield (rh, pa)
    def f[A](iter: Iterable[(Int, A)]): Seq[Seq[A]] = {
      val map = iter.groupMap(_._1)(_._2).withDefaultValue(Iterable.empty)
      Seq.tabulate(rel.parikhAutomata.length) { i => map(i).toSeq }
    }
    rel.lazyIntersect(ParikhRelation(f(rhsPa), phi))
  }

}
