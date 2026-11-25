import MatharThreeColumns.Statement
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Ring

/-!
# Mathar's three-column formula

Each column support is a set of at most two rows. For three such columns, mark a row
that belongs to all three supports. There are n choices of marked row and n choices
of support containing it in each column, hence n⁴ marked pairs. Two common rows
determine the whole matrix. Correcting that double count proves the formula.

The matrix encoding follows OpenAI's indexed Boolean matrices. The statement lives
in a separate module following Anthropic's specification. The proof of Lemma 2.2(1)
in the Google Research paper gives a related example of counting marked objects twice.

## 日本語

1が立つ行を高々2個選ぶ方法が、各列に p = 1 + n + n.choose 2 通りある。
3列を独立に選んだ p³ 個の行列で、3列すべてが1の行に印を付ける。
特定の行を指定すると、各列はその行だけを使うか、残りのどれか1行も使う。
したがって印付きの行列は n · n³ 個ある。2行とも印が付く場合、どの列も
その2行だけを使うので、行の組ごとに行列が1個に定まる。3行に印が付く
ことはない。包除原理から T(n,3) + n⁴ = p³ + n.choose 2 が従う。

形式化では、OpenAI の順序付き0–1行列の型を長方形に拡張し、Anthropic の例に
従って問題文を独立に読めるモジュールに置いた。Google の辺再構成論文の補題
2.2(1)にある、対象と印を組にして二通りに数える方法を、行と行列の組に用いた。

* [OpenAI, MatrixRemoval.lean](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatrixRemoval.lean#L9)
* [Google Research, edge reconstruction, Lemma 2.2](https://github.com/google-research/google-research/blob/4a7bc8ab0bc7/cogentic_research_papers/edge_reconstruction/paper.pdf)
* [Anthropic, EndStatement.lean](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/EndStatement.lean)
-/

namespace MatharThreeColumns

open Finset

private abbrev Column (n : ℕ) := {s : Finset (Fin n) // s.card ≤ 2}
private abbrev Columns (n : ℕ) := Fin 3 → Column n

/-- Row indices that appear in all three column supports. -/
private def common {n : ℕ} (c : Columns n) : Finset (Fin n) :=
  univ.filter fun i => ∀ j, i ∈ (c j).val

@[simp] private lemma mem_common {n : ℕ} {c : Columns n} {i : Fin n} :
    i ∈ common c ↔ ∀ j, i ∈ (c j).val := by simp [common]

private lemma row_bound (s : Finset (Fin 3)) : s.card ≤ 2 ↔ ¬ ∀ j, j ∈ s := calc
  _ ↔ s.card < Fintype.card (Fin 3) := by simp only [Fintype.card_fin]; omega
  _ ↔ s ≠ univ := s.card_lt_iff_ne_univ
  _ ↔ _ := not_congr ⟨fun h j => h ▸ mem_univ j, eq_univ_of_forall⟩

private def entries {n : ℕ} (c : Columns n) : BinaryMatrix n 3 :=
  fun i j => decide (i ∈ (c j).val)

@[simp] private lemma columnOnes_entries {n : ℕ} (c : Columns n) (j : Fin 3) :
    columnOnes (entries c) j = (c j).val := by ext i; simp [columnOnes, entries]

/-- Recover the actual Boolean matrix from its column supports, in both directions. -/
private def matrixEquiv (n : ℕ) :
    {A : BinaryMatrix n 3 // Admissible A} ≃ {c : Columns n // (common c).card = 0} where
  toFun a := ⟨fun j => ⟨columnOnes a.val j, a.property.2 j⟩, by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    apply (row_bound _).mp (a.property.1 i)
    simpa [rowOnes, columnOnes] using mem_common.mp hi⟩
  invFun c := ⟨entries c.val, by
    constructor
    · intro i
      apply (row_bound _).mpr
      intro hall
      have hi : i ∈ common c.val := mem_common.mpr (by simpa [rowOnes, entries] using hall)
      rw [card_eq_zero.mp c.property] at hi
      exact notMem_empty _ hi
    · intro j
      rw [columnOnes_entries]
      exact (c.val j).property⟩
  left_inv a := by
    apply Subtype.ext
    funext i j
    simp [entries, columnOnes]
  right_inv c := by
    apply Subtype.ext
    funext j
    exact Subtype.ext (columnOnes_entries c.val j)

private lemma column_card (n : ℕ) : Fintype.card (Column n) = 1 + n + n.choose 2 := by
  have split (s : Finset (Fin n)) :
      (if s.card ≤ 2 then 1 else 0 : ℕ) =
      (if s.card = 0 then 1 else 0) + (if s.card = 1 then 1 else 0) +
        (if s.card = 2 then 1 else 0) := by split_ifs <;> omega
  have h := sum_congr (s₁ := univ) rfl (fun s _ => split s)
  simpa [Column, Fintype.card_subtype, sum_add_distrib] using h

/-- A column containing row i is uniquely specified by its other row, using i for a singleton. -/
private def containing {n : ℕ} (i j : Fin n) : {s : Column n // i ∈ s.val} :=
  ⟨⟨{i, j}, card_le_two⟩, by simp⟩

private lemma containing_card {n : ℕ} (i : Fin n) :
    Fintype.card {s : Column n // i ∈ s.val} = n := by
  have bij : Function.Bijective (containing i) := by
    constructor
    · intro j k h
      have eq : ({i, j} : Finset (Fin n)) = {i, k} :=
        congrArg (fun s : {s : Column n // i ∈ s.val} => s.val.val) h
      have hj : j ∈ ({i, k} : Finset _) := eq ▸ (by simp : j ∈ ({i, j} : Finset _))
      have hk : k ∈ ({i, j} : Finset _) := eq.symm ▸ (by simp : k ∈ ({i, k} : Finset _))
      simp only [mem_insert, mem_singleton] at hj hk
      grind
    · rintro ⟨⟨s, hs⟩, hi⟩
      by_cases h : ∃ j ∈ s, j ≠ i
      · obtain ⟨j, hj, hji⟩ := h
        refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
        change {i, j} = s
        apply eq_of_subset_of_card_le
        · exact insert_subset hi (singleton_subset_iff.mpr hj)
        · simpa [card_pair hji.symm] using hs
      · refine ⟨i, Subtype.ext (Subtype.ext ?_)⟩
        change {i, i} = s
        ext j
        simp only [mem_insert, mem_singleton, or_self]
        exact ⟨fun e => e ▸ hi, fun hj => by_contra fun hji => h ⟨j, hj, hji⟩⟩
  simpa using (Fintype.card_congr (Equiv.ofBijective _ bij)).symm

private lemma common_subset {n : ℕ} (c : Columns n) (j : Fin 3) : common c ⊆ (c j).val :=
  fun _ hi => mem_common.mp hi j

private lemma common_le_two {n : ℕ} (c : Columns n) : (common c).card ≤ 2 :=
  (card_le_card (common_subset c 0)).trans (c 0).property

@[simp] private lemma common_const {n : ℕ} (s : Column n) :
    common (fun _ => s) = s.val := by ext; simp

/-- If two rows violate the row bound, every column consists of that same pair. -/
private def pairEquiv (n : ℕ) :
    {c : Columns n // (common c).card = 2} ≃ {s : Finset (Fin n) // s.card = 2} where
  toFun c := ⟨common c.val, c.property⟩
  invFun s := ⟨fun _ => ⟨s.val, s.property.le⟩, by simp [s.property]⟩
  left_inv c := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    exact eq_of_subset_of_card_le (common_subset c.val j) (by rw [c.property]; exact (c.val j).property)
  right_inv s := Subtype.ext (common_const ⟨s.val, s.property.le⟩)

private lemma at_row {n : ℕ} (i : Fin n) :
    (∑ c : Columns n, if i ∈ common c then 1 else 0 : ℕ) = n ^ 3 := calc
  _ = Fintype.card {c : Columns n // ∀ j, i ∈ (c j).val} := by simp [Fintype.card_subtype]
  _ = Fintype.card (Fin 3 → {s : Column n // i ∈ s.val}) := Fintype.card_congr
    (Equiv.subtypePiEquivPi (β := fun _ : Fin 3 => Column n) (p := fun _ s => i ∈ s.val))
  _ = _ := by simp [containing_card]

private lemma marked_rows (n : ℕ) : (∑ c : Columns n, (common c).card) = n ^ 4 := calc
  _ = ∑ c : Columns n, ∑ i : Fin n, if i ∈ common c then 1 else 0 := by
    apply sum_congr rfl
    intro c _
    rw [sum_boole]
    simp [common]
  _ = ∑ i : Fin n, ∑ c : Columns n, if i ∈ common c then 1 else 0 := sum_comm
  _ = ∑ _i : Fin n, n ^ 3 := sum_congr rfl fun i _ => at_row i
  _ = _ := by simp [pow_succ, mul_comm]

/-- Inclusion-exclusion for full rows. The equality is written without natural subtraction. -/
theorem count_three_columns (n : ℕ) :
    T n 3 + n ^ 4 = (1 + n + n.choose 2) ^ 3 + n.choose 2 := by
  have pointwise (c : Columns n) :
      (if (common c).card = 0 then 1 else 0 : ℕ) + (common c).card =
        1 + (if (common c).card = 2 then 1 else 0) := by
    have := common_le_two c
    split_ifs <;> omega
  have none : (∑ c : Columns n, if (common c).card = 0 then 1 else 0 : ℕ) = T n 3 := by
    simpa [T, Fintype.card_subtype] using (Fintype.card_congr (matrixEquiv n)).symm
  have two : (∑ c : Columns n, if (common c).card = 2 then 1 else 0 : ℕ) = n.choose 2 := by
    have h := (Fintype.card_congr (pairEquiv n)).trans (Fintype.card_finset_len 2)
    simpa [Fintype.card_subtype] using h
  have total : (∑ _c : Columns n, 1 : ℕ) = (1 + n + n.choose 2) ^ 3 := by
    simp [Columns, column_card]
  have h := sum_congr (s₁ := univ) rfl fun c _ => pointwise c
  simpa only [sum_add_distrib, none, two, marked_rows, total] using h

/-- The exact rational polynomial conjectured by Mathar, for every natural row count. -/
theorem mathar_A401159_three_columns : Conjecture := by
  intro n
  have h : (T n 3 : ℚ) + (n : ℚ)^4 =
      (1 + (n : ℚ) + (n.choose 2 : ℚ))^3 + (n.choose 2 : ℚ) := by
    exact_mod_cast count_three_columns n
  rw [Nat.cast_choose_two] at h
  calc
    _ = _ := eq_sub_of_add_eq h
    _ = _ := by ring

end MatharThreeColumns
