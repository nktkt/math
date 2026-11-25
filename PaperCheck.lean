import MatharThreeColumns

/-! Check the paper's displayed polynomial directly against a count of Boolean matrices. -/

open Finset

example (n : ℕ) :
    8 * (Fintype.card {A : Fin n → Fin 3 → Bool //
      (∀ i, (univ.filter fun j => A i j = true).card ≤ 2) ∧
      (∀ j, (univ.filter fun i => A i j = true).card ≤ 2)} : ℚ) =
      (n : ℚ)^6 + 3*(n : ℚ)^5 + (n : ℚ)^4 + 13*(n : ℚ)^3 +
        22*(n : ℚ)^2 + 8*(n : ℚ) + 8 := by
  change 8 * (MatharThreeColumns.T n 3 : ℚ) = _
  rw [MatharThreeColumns.mathar_A401159_three_columns n]
  ring

#print axioms MatharThreeColumns.count_three_columns
#print axioms MatharThreeColumns.mathar_A401159_three_columns
