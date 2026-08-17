import Delta.Basic
import Mathlib.Tactic

namespace Delta

namespace DeltaCondition

/-- A valid witness lies strictly below its centre, so `ℕ` subtraction is exact. -/
theorem lt_center {p δ : ℕ} (h : DeltaCondition p δ) : δ < p + 1 := by
  have hLower : Nat.Prime (p + 1 - δ) := h.2.2.1
  have hPositive : 0 < p + 1 - δ := hLower.pos
  omega

/-- The two symmetric primes add to the centre even number from the paper. -/
theorem sum_eq {p δ : ℕ} (h : DeltaCondition p δ) :
    (p + 1 - δ) + (p + 1 + δ) = 2 * p + 2 := by
  have hδ := h.lt_center
  omega

/-- Package the prime pair and its Goldbach sum in one reusable statement. -/
theorem goldbach_pair {p δ : ℕ} (h : DeltaCondition p δ) :
    Nat.Prime (p + 1 - δ) ∧
      Nat.Prime (p + 1 + δ) ∧
      (p + 1 - δ) + (p + 1 + δ) = 2 * p + 2 := by
  exact ⟨h.2.2.1, h.2.2.2, h.sum_eq⟩

end DeltaCondition

/-- The smallest non-exceptional cousin-prime pair has the witness `δ = 3`. -/
theorem deltaCondition_seven_three : DeltaCondition 7 3 := by
  norm_num [DeltaCondition]

/-- The pair `(37, 41)` demonstrates that the first offset need not work. -/
theorem deltaCondition_thirtySeven_nine : DeltaCondition 37 9 := by
  norm_num [DeltaCondition]

/-- The pair `(3, 7)` has no Δ witness. -/
theorem no_deltaCondition_three : ¬ ∃ δ : ℕ, DeltaCondition 3 δ := by
  rintro ⟨δ, hδ⟩
  have hlt : δ < 4 := by simpa using hδ.lt_center
  rcases hδ.1 with ⟨k, hk⟩
  rcases hδ.2.1 with ⟨m, hm⟩
  have hδeq : δ = 3 := by omega
  norm_num [DeltaCondition, hδeq] at hδ

/-- Consequently, the literal universal version of the conjecture is false. -/
theorem not_rawDeltaConjecture : ¬ RawDeltaConjecture := by
  intro h
  apply no_deltaCondition_three
  exact h 3 (by norm_num [IsCousinPrime])

end Delta
