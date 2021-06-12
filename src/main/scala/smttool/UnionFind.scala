package com.github.kmn4.expresso.smttool

private[smttool] trait UnionFind[A] extends PartialFunction[A, A] {
  // union と find の引数は既に make されていることを仮定
  def union(x: A, y: A): Unit
  def find(x: A): A
  def make(x: A): Unit
}

// ナイーブな実装．悪質な入力に対しては効率が悪い
object PrioUnionFind {
  private class Tree[A](val elem: A) {
    private var parent: Option[Tree[A]] = None
    def root: Tree[A] = parent match {
      case Some(t) => t.root
      case None    => this
    }
    def setParent(newParent: Tree[A]) = parent = Some(newParent)
  }

  def apply[A](f: (A, A) => Either[Unit, Unit])(xs: A*): UnionFind[A] =
    new UnionFind[A] {

      override def apply(v1: A): A = find(v1)

      override def isDefinedAt(x: A): Boolean = trees.isDefinedAt(x)

      private val trees = collection.mutable.Map.empty[A, Tree[A]]
      for (x <- xs) trees(x) = new Tree(x)

      private def findRoot(x: A): Tree[A] = trees(x).root

      override def union(x: A, y: A): Unit = {
        val xRoot = findRoot(x)
        val yRoot = findRoot(y)
        f(xRoot.elem, yRoot.elem) match {
          case Left(())  => yRoot.setParent(xRoot)
          case Right(()) => xRoot.setParent(yRoot)
        }
      }

      override def find(x: A): A = findRoot(x).elem

      override def make(x: A): Unit =
        trees.getOrElseUpdate(x, new Tree(x))

    }
}
