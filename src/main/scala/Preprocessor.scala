package com.github.kmn4.expresso
import smtlib.trees.Commands
import smtlib.trees.Terms
import smtlib.theories.Ints
import smtlib.theories.Core
import smtlib.trees.TreeTransformer
import smtlib.trees.Tree
import com.github.kmn4.expresso.smttool._

// PyEx 用
// SMT-LIB コマンド列の変換
class Preprocessor(provider: VarProvider) {

  private class Flattener(
      // パターンとして使う．
      // 特定の文字列操作 (例えば substr, indexof, replace) であるかどうか判定する．
      // (substr _ _ _) -(unapply)-> StringSort
      StringOp: PartialFunction[Terms.Term, Terms.Sort]
  ) {
    // あらゆるメソッド呼び出しで registerSort が呼ばれる点に注意

    private val sorts = SortStore()

    private def registerSort(x: String, sort: Terms.Sort): Unit =
      sorts.register(x, sort)

    private def sortMap(ss: Iterable[String]): Map[String, Terms.Sort] =
      sorts.mapOf(ss)

    // (replace (replace x y z) w (substr x i j)) のような項を
    // (replace x1 w x2), ((x1, (replace x y z)), (x2, (substr x i j)))
    // のように変形する
    private val flatTermBinder = new BottomUpTermTransformer {
      type R = Seq[(String, Terms.Term)]

      override def combine(results: Seq[R]): R = results.flatten

      override def post(term: Terms.Term, result: R): (Terms.Term, R) =
        term match {
          case StringOp(sort) if result.isEmpty =>
            val x = provider.freshTemp()
            registerSort(x, sort)
            (SimpleQualID(x), Seq((x, term)))
          case _ => (term, result)
        }
    }

    private def bindInnermostFlatTerms(term: Terms.Term) = flatTermBinder.transform(term, ())

    // f が必ずしも (A => B, A => Seq[C]) へと分解できない場合に使う
    def mapAndFlatMap[A, B, C](f: A => (B, Seq[C])): Seq[A] => (Seq[B], Seq[C]) =
      s =>
        s.foldLeft((Seq.empty[B], Seq.empty[C])) {
          case ((accB, accC), a) =>
            val (b, cs) = f(a)
            (accB :+ b, accC ++ cs)
        }

    private val bindInnermost = mapAndFlatMap(bindInnermostFlatTerms)

    private def chooseRepr[A](cc: Iterable[A]): (A, Map[A, A]) = {
      val repr = cc.head
      val map = cc.map((a: A) => a -> repr).toMap
      (repr, map)
    }

    private def chooseRepresentative[A, B](
        // 仮定: Iterable[B] は非空で，どの2つの Iterable[B] も共通部分が空
        map: Map[A, Iterable[B]]
    ): (Map[A, B], Map[B, B]) = {
      map.foldLeft((Map.empty[A, B], Map.empty[B, B])) {
        case ((accA, accB), (a, bb)) =>
          val (b, bMap) = chooseRepr(bb)
          (accA + (a -> b), accB ++ bMap)
      }
    }

    private def flattenOnce(terms: Seq[Terms.Term]): (
        Seq[Terms.Term], // terms の最内平坦項を変数に置き換えたもの
        Seq[(String, Terms.Term)] // (変数 x, 項 t) で x = t を表す
    ) = {
      val (absTerms, bindings) = bindInnermost(terms)
      val grouped = bindings.groupMap(_._2)(_._1)
      val (termVar, varRepr) = chooseRepresentative(grouped)
      val substVars = subst {
        case SimpleQualID(name) if varRepr.isDefinedAt(name) =>
          SimpleQualID(varRepr(name))
      }
      val resTerms = absTerms.map(substVars)
      val assigns = termVar.iterator.map { case (t, x) => (x, t) }.toSeq
      (resTerms, assigns)
    }

    def flatten(terms: Seq[Terms.Term]): (
        Seq[(String, Terms.Term)], // x = t (代入等式)
        Seq[Terms.Term], // x = y, x = w, i + j < c など (リテラル)
        Map[String, Terms.Sort] // このメソッドで新たに導入した変数のソート
    ) = {
      var assigns = Seq.empty[(String, Terms.Term)]
      def aux(terms: Seq[Terms.Term]): Seq[Terms.Term] = {
        val (flattened, newAssigns) = flattenOnce(terms)
        if (newAssigns.isEmpty) terms
        else {
          assigns ++= newAssigns
          aux(flattened)
        }
      }
      val flattened = aux(terms)
      (assigns, flattened, sortMap(assigns.map(_._1)))
    }
  }

  private[expresso] def flatten(terms: Seq[Terms.Term]) = {
    val operations: PartialFunction[Terms.Term, Terms.Sort] = {
      case Strings.Concat(_*)         => Strings.StringSort()
      case Strings.At(_, _)           => Strings.StringSort()
      case Strings.IndexOf(_, _, _)   => Ints.IntSort()
      case Strings.Length(_)          => Ints.IntSort()
      case Strings.Replace(_, _, _)   => Strings.StringSort()
      case Strings.Substring(_, _, _) => Strings.StringSort()
    }
    val flattener = new Flattener(operations)
    flattener.flatten(terms)
  }

  private object Folder {
    private val numeralZero = Terms.SNumeral(BigInt(0))
    private def foldOnce(term: Terms.Term): Terms.Term = term match {
      case Ints.Add(`numeralZero`, t) => t
      case Ints.Add(t, `numeralZero`) => t
      case Ints.Sub(t, `numeralZero`) => t
      case _                          => term
    }

    private val transformer = new BottomUpTermTransformer {
      type R = Unit
      override def post(term: Terms.Term, result: Unit): (Terms.Term, Unit) =
        (foldOnce(term), ())
      override def combine(results: Seq[Unit]): Unit = ()
    }

    def fold(term: Terms.Term): Terms.Term = transformer.transform(term, ())._1
  }
  def fold(terms: Seq[Terms.Term]): Seq[Terms.Term] =
    terms.map(term => Folder.fold(term))

  private object Optimizer {
    private val zeroNumeral = Terms.SNumeral(BigInt(0))
    private def optimizeRoot(term: Terms.Term): Seq[Terms.Term] = term match {
      // (str.at t n) = c ==> t ∈ Σ^n c Σ^*
      case Core.Equals(Strings.At(t, Terms.SNumeral(n)), Terms.SString(c)) if n >= 0 && c.length == 1 =>
        val pre =
          Strings.Regex.Power(Strings.Regex.AllChar(), Terms.SNumeral(n))
        val cr = Strings.ToRegex(Terms.SString(c))
        val post = Strings.Regex.All()
        Seq(Strings.InRegex(t, Strings.Regex.Concat(pre, cr, post)))
      // (str.at t (- (str.len t) n)) = c ==> t ∈ Σ^* c Σ^{n-1}
      case Core.Equals(
          Strings.At(t1, Ints.Sub(t2, Terms.SNumeral(n))),
          Terms.SString(c)
          ) if n - 1 >= 0 && c.length == 1 && t1 == t2 /* TODO 効率？ */ =>
        val pre = Strings.Regex.All()
        val cr = Strings.ToRegex(Terms.SString(c))
        val post =
          Strings.Regex.Power(Strings.Regex.AllChar(), Terms.SNumeral(n - 1))
        Seq(Strings.InRegex(t1, Strings.Regex.Concat(pre, cr, post)))
      case _ => Seq(term)
    }
    private def optimizeOnce(term: Terms.Term): Terms.Term = term match {
      // FIXME optimize をボトムアップ化
      case Strings.Substring(t1, `zeroNumeral`, Strings.Length(t2)) if t1 == t2 /* TODO 効率？ */ =>
        t1
      case _ => term
    }
    private def optimize(term: Terms.Term): Seq[Terms.Term] = ???
    // TODO optimizeOnce
    def optimize(assertion: Commands.Assert): Seq[Commands.Assert] =
      optimize(assertion.term).map(Commands.Assert.apply)
  }
  def optimize(assertions: Seq[Commands.Assert]): Seq[Commands.Assert] =
    assertions.flatMap(assertion => Optimizer.optimize(assertion))

  // PyEx-{td,z3,zz} を EXPRESSO が解ける形に変換する
  def preprocess(argCommands: Seq[Commands.Command]): Seq[Commands.Command] = {
    var commands = argCommands
    // (check-sat), (get-model) が最後以外に現れるものは考えない
    val getModel = commands.indexWhere(_.isInstanceOf[Commands.GetModel])
    val checkSat = commands.indexWhere(_.isInstanceOf[Commands.CheckSat])
    require {
      (checkSat == -1 && getModel == -1) || // 両方ない
      (checkSat == commands.length - 1 && getModel == -1) || // (check-sat) が最後
      (checkSat + 1 == getModel && getModel == commands.length - 1) // (check-sat), (get-model)
    }

    // ユーザー宣言変数にプレフィックスを加える
    commands = {
      val vars = SortStore(commands: _*).map.keySet
      val f: PartialFunction[Terms.Term, Terms.Term] = {
        case SimpleQualID(x) if vars(x) => SimpleQualID(provider.UserVar(x))
      }
      val prefixer = new SubstTransformer(f) {
        // (declare-const name sort) において name は SSymbol であり Term ではないので，
        // SSymbol 用に定義し直さなければならない．
        override def transformSymbol(symbol: Terms.SSymbol, context: C): (Terms.SSymbol, R) = {
          val x = symbol.name
          val newSym = if (vars(x)) Terms.SSymbol(provider.UserVar(x)) else symbol
          (newSym, combine(symbol, context, Seq()))
        }
      }
      commands.map(prefixer.transform(_, ())).map(_._1)
    }

    // - (= (ite b 0 1) 0) のような式を b などに置き換える
    // - 二重否定を除く
    // - str.at を str.substr に変換する
    // - (and (and (and ...) b) b) から b のリストを取り出す
    val simplify = compose(elimITE, elimDoubleNegation)
    var bools = commands.flatMap {
      case Commands.Assert(t) =>
        val simpl = simplify(t)
        andToTerms(simpl)
      case cmd => Seq()
    }

    // declare-{const,fun} の宣言を覚えておく
    val sorts = SortStore(commands: _*)

    // (not (= x w)) => (str.in.re x (re.comp (str.to.re w))) のような変換
    bools = bools.map {
      case RegexConstraint(name, re) => RegexConstraint(name, re)
      case t                         => t
    }

    // 制約に現れる文字列操作を変数に置き換える．
    val (assigns, literals, newSorts) = flatten(bools)
    newSorts.foreach { case (name, sort) => sorts.register(name, sort) }

    val lhsVars = assigns.iterator.map { case (x, _) => x }.toSet
    // literals の内 x = y (文字列変数の等式) が冗長．
    // 1. 等式から文字列変数の同値類を構成する．
    //    同値類に含まれる左辺変数は高々1つでなければならない (直線性より)．
    // 2. 同値類について代表元を決める．左辺変数があるならそれが代表元になる．
    // 3. 各変数を代表元に置き換える．
    val uf = PrioUnionFind[String] {
      case (x, y) if lhsVars(x) && lhsVars(y) =>
        throw new Exception("not straight-line")
      case (x, y) if lhsVars(y) => Right(())
      case _                    => Left(())
    }()
    val StringVariable: PartialFunction[Terms.Term, String] = {
      val sortsMap = sorts.map
      val string = Strings.StringSort()

      { case SimpleQualID(name) if sortsMap(name) == string => name }
    }
    // 1., 2.
    for (Core.Equals(StringVariable(x), StringVariable(y)) <- literals) {
      uf.make(x)
      uf.make(y)
      uf.union(x, y)
    }
    // 3.
    // 次のような例があるので，assigns にも substVars する.
    // (= x (f x))
    // =[flatten]=> assign: (= x1 (f x)), literal: (= x x1)
    // =[union-find]=> x -> x1
    val substVars = subst {
      case SimpleQualID(name) if uf.isDefinedAt(name) => SimpleQualID(uf(name))
    }
    val literalBools = literals.flatMap {
      case Core.Equals(StringVariable(x), StringVariable(y)) => None
      case term                                              => Some(substVars(term))
    }
    val assignBools = assigns.map { case (x, t) => substVars(Core.Equals(SimpleQualID(x), t)) }
    bools = assignBools ++ literalBools

    val decls = sorts.map.iterator.map {
      case (x, sort) =>
        Commands.DeclareConst(Terms.SSymbol(x), sort)
    }
    val check = if (checkSat >= 0) Some(Commands.CheckSat()) else None
    val get = if (getModel >= 0) Some(Commands.GetModel()) else None
    (decls ++ bools.distinct.map(Commands.Assert.apply) ++ check ++ get).toSeq
  }
  // def preprocess

}
