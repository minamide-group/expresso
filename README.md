# Usage
`java -jar JARFILE CONSTRAINT [STRATEGY]`
- CONSTRAINT は `.smt2` ファイル
- STRATEGY は `preimage` または `jssst`
    - `jssst` は JSSST2021大会予稿で示したアルゴリズム（デフォルト）
    - `preimage` は OSTRICH 風の逆像計算によるアルゴリズム

# インストール
## Docker を使う場合
```bash
docker pull kamasaki/expresso:jssst2021
```

使い方
```bash
docker run --rm -i -v $(pwd):/workdir kamasaki/expresso:jssst2021 CONSTRAINT [STRATEGY]
```

## 手動ビルド

`sbt assembly` する．
ビルド時と実行時に以下の依存性がある．

### [Z3](https://github.com/Z3Prover/z3)
配布しているバイナリはバージョン
[4.8.8](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.8)
の Z3 を利用している．
リンクから環境に応じた Zip ファイルをダウンロードする．

`/bin` ディレクトリから次のファイルを適切な場所 (`/usr/lib` など) にコピーする．
- `libz3.so`
- `libz3java.so`

また Z3 の `/bin/com.microsoft.z3.jar` をビルドディレクトリの `lib/` に配置する．

### [scala-smtlib](https://github.com/regb/scala-smtlib)
Scala 2.13 対応のバイナリは自動で解決されないので，自分でビルドしたものを `lib/` 以下に配置
([ビルド方法](https://github.com/regb/scala-smtlib#building-the-sources))．

# 制約
[./constraints](./constraints/) 以下に制約例がある．
[./constraints/bench](./constraints/bench/) の例 (の多く) は [ParikhSolverTest](./src/test/scala/ParikhSolverTest.scala) クラスから実行される．
JSSST2021大会予稿に例として取り上げた制約は以下：
- [indexof2_sat](./constraints/bench/indexof2_sat.smt2)
- [indexof2_unsat](./constraints/bench/indexof2_unsat.smt2)
- [deleteall](./constraints/bench/deleteall.smt2)
- [substr_equiv](./constraints/bench/substr_equiv.smt2)
- [inverse_sat](./constraints/bench/inverse_sat.smt2)
- [inverse_unsat](./constraints/bench/inverse_unsat.smt2)

