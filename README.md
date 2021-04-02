# Usage
`java -jar JARFILE CONSTRAINT STRATEGY`
- CONSTRAINT は `.smt2` ファイル
- STRATEGY は `preimage` または `thesis`
    - `preimage` は逆像計算によるアルゴリズム
    - `thesis` は卒論でも使った合成に基づくアルゴリズム

SBT でテストを実行すると `./constraints/bench/log` にソルバーのログが記録される．

# 実行時の依存性
Z3 のライブラリが必要．
- `libz3.so`
- `libz3java.so`

## Z3 のビルド
```sh
git clone https://github.com/Z3Prover/z3.git
cd z3
python3 scripts/mk_make.py --java
make install
```

環境変数 `JNI_HOME` が `jni.h` を含むディレクトリであることが必要．
例えば Ubuntu では `python3 scripts/mk_make.py --java` の代わりに
`env JNI_HOME=/usr/lib/jvm/java-11-openjdk-amd64/include python3 scripts/mk_make.py --java` とする．

# 制約
[./constraints](./constraints/) 以下に制約例がある．
[./constraints/bench](./constraints/bench/) の例 (の多く) は [ParikhSolverTest](./src/test/scala/ParikhSolverTest.scala) クラスから実行される．
いずれかの戦略で 100 ミリ秒以上かかる制約の実行時間を表に示す．
値は ParikhSolverTest を実行したとき withInfoTime メソッドによって表示されるもの．
表は実行時間の比によってソートされている．

| constraint                                                            | sat | thesis | preimage | preimage / thesis |
|-----------------------------------------------------------------------|-----|--------|----------|-------------------|
| [insert_script](./constraints/bench/insert_script.smt2)               | y   |   4308 |       63 |       0.014623955 |
| [deleteall](./constraints/bench/deleteall.smt2)                       | y   |   2006 |      101 |       0.050348953 |
| [concat_delete](./constraints/bench/concat_delete.smt2)               | y   |   7771 |      518 |       0.066658088 |
| [concat_unsat_03](./constraints/bench/concat_unsat_03.smt2)           | n   |    211 |       15 |       0.071090047 |
| [group_sc](./constraints/bench/group_sc.smt2)                         | y   |   3667 |      698 |        0.19034633 |
| [cat_pre_suf](./constraints/bench/cat_pre_suf.smt2)                   | n   |   1161 |     1031 |        0.88802756 |
| [substr_equiv](./constraints/bench/substr_equiv.smt2)                 | n   |    920 |     1835 |         1.9945652 |
| [concat_prefix_suffix](./constraints/bench/concat_prefix_suffix.smt2) | n   |   2234 |     5638 |         2.5237243 |
| [indexof](./constraints/bench/indexof.smt2)                           | n   |     55 |      163 |         2.9636364 |
| [for_slide](./constraints/bench/for_slide.smt2)                       | y   |    248 |     1274 |         5.1370968 |

- preimage が速い
  + insert_script
  + deleteall
  + concat_delete
  + concat_unsat_xx
  + group_sc
- preimage が遅い
  + substr_equiv
  + for_slide
- preimage は substr と連接を含む unsat な制約が遅い傾向
- constraints/concat_unsat_xx は [Zhu2019] (修論) より.
  + xx が大きいほど多くのコピーが作られる
  + thesis では 04 がすでに厳しい
  + preimage では指数的に実行時間が伸びるが少し待てば 09 も止まる
  + 決定性 SST のソルバは preimage より速い
- for_slide は卒論のスライドで例示したもの
  + substr と連接で insert 関数を模倣
  + ほぼ等価な制約として `constraints/bench/insert_opt.smt2` がある
    - insert 関数を使う
    - 戦略 preimage のみが扱える
    - 戦略 thesis が制約 for_slide を解くより少し速い

## 100 ミリ秒以下で終わる制約 (ベンチマークというよりテスト)
| constraint                                                              | sat | thesis | preimage | preimage / thesis |
|-------------------------------------------------------------------------|-----|--------|----------|-------------------|
| [replace_some_2](./constraints/bench/replace_some_2.smt2)               | n   |     34 |       16 |        0.47058824 |
| [indexof_sat](./constraints/bench/indexof_sat.smt2)                     | y   |     82 |       41 |               0.5 |
| [replaceall_int](./constraints/bench/replaceall_int.smt2)               | y   |     68 |       40 |        0.58823529 |
| [reverse_indexof_sat](./constraints/bench/reverse_indexof_sat.smt2)     | y   |     40 |       27 |             0.675 |
| [pcre_precedence_sat](./constraints/bench/pcre_precedence_sat.smt2)     | y   |     41 |       28 |        0.68292683 |
| [replace_some_1](./constraints/bench/replace_some_1.smt2)               | y   |     46 |       37 |        0.80434783 |
| [pcre_precedence_unsat](./constraints/bench/pcre_precedence_unsat.smt2) | n   |     63 |       64 |         1.0158730 |
| [substr_zip_sat](./constraints/bench/substr_zip_sat.smt2)               | y   |     25 |       33 |              1.32 |
| [substr_zip_unsat](./constraints/bench/substr_zip_unsat.smt2)           | n   |     25 |       56 |              2.24 |
| [reverse_indexof_unsat](./constraints/bench/reverse_indexof_unsat.smt2) | n   |     28 |       64 |         2.2857143 |
# ビルドの依存性
## Z3
`lib/` に `com.microsoft.z3.jar` が必要．
Z3 をビルドすると生成される `build/com.microsoft.z3.jar` をコピーすればよい．

## [scala-smtlib](https://github.com/regb/scala-smtlib)
Scala 2.13 対応のバイナリは自動で解決されないので，自分でビルドしたものを `lib/` 以下に配置
([ビルド方法](https://github.com/regb/scala-smtlib#building-the-sources))．

