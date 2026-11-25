import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs

/-!
# Richard J. Mathar's three-column conjecture

Mathar posted the polynomial for three columns in OEIS A401159 on 18 November 2026.
His 2014 paper defines the matrices, gives a general recurrence, and tabulates the first
values in Table 2. In the triangular display, the third column starts at three rows.
The finite matrix definition below also makes sense with zero, one, or two rows.

* [OEIS statement, fixed revision](https://github.com/oeis/oeisdata/blob/b460c2e8ffbef9a3aacf263819282712f0f30341/seq/A401/A401159.seq#L5-L10)
* [Mathar's paper, Definition 1 and Table 2](https://oeis.org/A247158/a247158.pdf)
-/

namespace MatharThreeColumns

open Finset

abbrev BinaryMatrix (n m : ℕ) := Fin n → Fin m → Bool

def rowOnes {n m : ℕ} (A : BinaryMatrix n m) (i : Fin n) : Finset (Fin m) :=
  univ.filter fun j => A i j = true

def columnOnes {n m : ℕ} (A : BinaryMatrix n m) (j : Fin m) : Finset (Fin n) :=
  univ.filter fun i => A i j = true

/-- Matrices are labeled. Permuting rows or columns can give a different matrix. -/
abbrev Admissible {n m : ℕ} (A : BinaryMatrix n m) : Prop :=
  (∀ i, (rowOnes A i).card ≤ 2) ∧ (∀ j, (columnOnes A j).card ≤ 2)

/-- Count the matrices directly, requiring both bounds on their Boolean entries. -/
def T (n m : ℕ) : ℕ := Fintype.card {A : BinaryMatrix n m // Admissible A}

def Conjecture : Prop :=
  ∀ n : ℕ, (T n 3 : ℚ) =
    1 + n + 11 * (n : ℚ)^2 / 4 + 13 * (n : ℚ)^3 / 8 +
      (n : ℚ)^4 / 8 + 3 * (n : ℚ)^5 / 8 + (n : ℚ)^6 / 8

end MatharThreeColumns
