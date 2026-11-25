# 行和・列和が高々2の3列二値行列の計数

[English](README.md) · **日本語** · [研究一覧](../../README.ja.md)

[日本語の論文（PDF）](output/pdf/three-columns-ja.pdf)・[英語の論文（PDF・主版）](output/pdf/three-columns.pdf)・[Leanの定理](MatharThreeColumns.lean)

$T(n,3)$ を、各行・各列に1が高々2個ある、行と列に番号の付いた $n$ 行3列の二値行列の個数とする。任意の非負整数 $n$ について次の等式が成り立つ。

$$
T(n,3)=\left(1+n+\binom{n}{2}\right)^3-n^4+\binom{n}{2}
=\frac{n^6+3n^5+n^4+13n^3+22n^2+8n+8}{8}.
$$

右辺の3乗は、各列で1を置く行の集合を独立に選んだ総数である。3列すべてが1の行を一つ指定した組は $n^4$ 個ある。そのような行が二つあれば、どの2行かを選ぶだけで全列が決まるので、該当する行列はちょうど $\binom{n}{2}$ 個となる。この重複を補正すると公式が得られる。

Richard J. Mathar は2026年11月18日、3列の場合の多項式をOEISで予想として公表した。同著者の2014年の論文には一般の漸化式と、3列の場合の7個の値が載っている。本稿の第3節では、次数が6以下であることとその7値からも公式を導く。証明の歴史的な初出は未確認である。[OEIS A401159の第9版](https://github.com/oeis/oeisdata/blob/b460c2e8ffbef9a3aacf263819282712f0f30341/seq/A401/A401159.seq#L10)・[Matharの2014年の論文、表2](https://oeis.org/A247158/a247158.pdf)

## Lean証明を検証する

Git、Make、`elan` が入った環境で次のコマンドを実行する。Leanは4.29.1に、mathlibは特定のコミットに固定している。

```sh
git clone https://github.com/nktkt/math.git
cd math/research/mathar_three_columns
make verify
```

このコマンドは証明をビルドし、論文の多項式を二値行列の定義と照合したうえで、証明とその依存項目を空のLeanカーネル環境から再検証する。主要な二つの定理が依存する公理は `propext`、`Classical.choice`、`Quot.sound` の3個である。

| ファイル | 内容 |
| --- | --- |
| [Statement.lean](MatharThreeColumns/Statement.lean) | 行と列に番号を付けた二値行列、個数 `T`、原文と同じ有理係数で書いた予想 |
| [MatharThreeColumns.lean](MatharThreeColumns.lean) | 包除公式 `count_three_columns` と最終定理 `mathar_A401159_three_columns` の証明 |
| [PaperCheck.lean](PaperCheck.lean) | 行列の成分から直接書き下した紙面の公式との照合と、依存公理の表示 |

## 英日両版の論文を再組版する

LuaLaTeX、LuaTeX-ja、`latexmk` のある環境で、この研究のフォルダから `make papers` を実行する。PDFは `output/pdf/` に出力される。両版は数式・数表・ベクトル図を共有している。[英語のLaTeX原稿](paper/three-columns.tex)・[日本語のLaTeX原稿](paper/three-columns-ja.tex)・[共通の数式と数表](paper/counting-data.tex)

図は組版用のPDFを同梱している。例に使う行列を変更する場合は、作図用スクリプトを編集し、ReportLab 4.4.9の環境で `python3 paper/marked_rows.py` を実行してから再組版する。[作図用スクリプト](paper/marked_rows.py)

## 参考資料と来歴

行列の表現にはOpenAIの有限添字上のブール行列を用いた。問題文を独立したモジュールに置く例としてAnthropicの形式仕様を、印を付けた対象を二通りに数える例としてGoogle Researchの辺再構成論文の補題2.2(1)の証明を参照した。[OpenAIの行列定義](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatrixRemoval.lean#L9)・[Anthropicの形式仕様](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/EndStatement.lean)・[Google Researchの論文](https://github.com/google-research/google-research/blob/4a7bc8ab0bc7/cogentic_research_papers/edge_reconstruction/paper.pdf)

日本語原稿とLean証明は `nktkt/lean-proof-ci` で最初に一式を公開した。原稿の作成と形式化にはOpenAI Codexを使用した。[以前の公開版](https://github.com/nktkt/lean-proof-ci/tree/d38b6e3ae78f4948b59632bcc2359b0cc50dbe64/research/mathar_three_columns)・[MITライセンス](../../LICENSE)
