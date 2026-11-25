# Counting three-column binary matrices with row and column sums at most two

**English** · [日本語](README.ja.md) · [All studies](../../README.md)

[Read the English paper (PDF)](output/pdf/three-columns.pdf) · [Japanese paper (PDF)](output/pdf/three-columns-ja.pdf) · [Lean theorem](MatharThreeColumns.lean)

Let $T(n,3)$ count labeled $n$-by-$3$ binary matrices with at most two ones in each row and each column. For every nonnegative integer $n$,

$$
T(n,3)=\left(1+n+\binom{n}{2}\right)^3-n^4+\binom{n}{2}
=\frac{n^6+3n^5+n^4+13n^3+22n^2+8n+8}{8}.
$$

The cube counts the matrices obtained by choosing the three column supports independently. Marking a row of three ones gives $n^4$ pairs of a matrix and a marked row. Exactly $\binom{n}{2}$ matrices have two such rows, since the pair determines every column. This gives the two correction terms.

Richard J. Mathar recorded the three-column polynomial as a conjecture on November 18, 2026. His 2014 note gives a general recurrence and seven values for three columns. Section 3 of the paper shows how those seven values determine the formula once its degree is bounded by six. The historical priority of a proof remains undetermined. [OEIS A401159, revision 9](https://github.com/oeis/oeisdata/blob/b460c2e8ffbef9a3aacf263819282712f0f30341/seq/A401/A401159.seq#L10) · [Mathar's 2014 note, Table 2](https://oeis.org/A247158/a247158.pdf)

## Verify the proof

With Git, Make, and `elan` installed, run the following commands. The repository pins Lean 4.29.1 and the mathlib revision.

```sh
git clone https://github.com/nktkt/math.git
cd math/research/mathar_three_columns
make verify
```

The command builds the proof, checks the displayed polynomial against the definition of an admissible Boolean matrix, and replays the proof and its imports in a fresh Lean kernel environment. The two main theorems depend on `propext`, `Classical.choice`, and `Quot.sound`.

| File | Contents |
| --- | --- |
| [Statement.lean](MatharThreeColumns/Statement.lean) | Labeled binary matrices, the counting function `T`, and Mathar's conjecture with its original rational coefficients |
| [MatharThreeColumns.lean](MatharThreeColumns.lean) | The inclusion–exclusion identity `count_three_columns` and the final theorem `mathar_A401159_three_columns` |
| [PaperCheck.lean](PaperCheck.lean) | A separate statement of the displayed formula directly in terms of matrix entries, and an axiom report |

## Rebuild the papers

Run `make papers` from this study directory with LuaLaTeX, LuaTeX-ja, and `latexmk` installed. The PDFs are written to `output/pdf/`. Both editions use the same displayed equations, data table, and vector figure. [English LaTeX source](paper/three-columns.tex) · [Japanese LaTeX source](paper/three-columns-ja.tex) · [Shared equations and table](paper/counting-data.tex)

The figure is included. To change the example matrices, edit the drawing script and run `python3 paper/marked_rows.py` with ReportLab 4.4.9 before rebuilding the papers. [Figure source](paper/marked_rows.py)

## Sources and provenance

The formalization uses labeled Boolean entries following OpenAI's matrix specification, a separate statement module following Anthropic's example, and double counting of marked objects as in the proof of Lemma 2.2(1) of Google Research's edge-reconstruction paper. [OpenAI matrix definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatrixRemoval.lean#L9) · [Anthropic statement module](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/EndStatement.lean) · [Google Research paper](https://github.com/google-research/google-research/blob/4a7bc8ab0bc7/cogentic_research_papers/edge_reconstruction/paper.pdf)

The Japanese note and Lean proof were first distributed together in `nktkt/lean-proof-ci`. OpenAI Codex assisted in preparing the manuscripts and formalization. [Earlier version](https://github.com/nktkt/lean-proof-ci/tree/d38b6e3ae78f4948b59632bcc2359b0cc50dbe64/research/mathar_three_columns) · [MIT license](../../LICENSE)
