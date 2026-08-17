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

namespace KDeltaCondition

/-- A valid `k`-coordinate has its offset strictly below the centre. -/
theorem offset_lt_center {p k : ℕ} (h : KDeltaCondition p k) :
    6 * k + 3 < p + 1 :=
  h.1

/--
A valid `k`-coordinate lies in a finite search range: it is strictly below
`(p - 3) / 6 + 1`.  The proof starts from the explicit natural-number bound
in `KDeltaCondition`, so the truncated subtraction in `p - 3` is accounted for.
-/
theorem k_lt_search_bound {p k : ℕ} (h : KDeltaCondition p k) :
    k < (p - 3) / 6 + 1 := by
  have hOffset : 6 * k + 3 < p + 1 := h.1
  omega

end KDeltaCondition

/-- Existence of a Δ offset is equivalent to existence of its `k`-coordinate. -/
theorem exists_deltaCondition_iff_exists_kDeltaCondition {p : ℕ} :
    (∃ δ : ℕ, DeltaCondition p δ) ↔ ∃ k : ℕ, KDeltaCondition p k := by
  constructor
  · rintro ⟨δ, hδ⟩
    have hlt : δ < p + 1 := hδ.lt_center
    have hOdd : Odd δ := hδ.1
    obtain ⟨m, hm⟩ := hδ.2.1
    subst δ
    have hmOdd : Odd m := Nat.Odd.of_mul_right hOdd
    obtain ⟨k, hk⟩ := hmOdd
    subst m
    refine ⟨k, ?_⟩
    change 6 * k + 3 < p + 1 ∧
      Nat.Prime (p - 2 - 6 * k) ∧
      Nat.Prime (p + 4 + 6 * k)
    refine ⟨?_, ?_, ?_⟩
    · omega
    · have hlower :
          p + 1 - 3 * (2 * k + 1) = p - 2 - 6 * k := by
        omega
      rw [← hlower]
      exact hδ.2.2.1
    · have hupper :
          p + 1 + 3 * (2 * k + 1) = p + 4 + 6 * k := by
        omega
      rw [← hupper]
      exact hδ.2.2.2
  · rintro ⟨k, hkDelta⟩
    change 6 * k + 3 < p + 1 ∧
      Nat.Prime (p - 2 - 6 * k) ∧
      Nat.Prime (p + 4 + 6 * k) at hkDelta
    rcases hkDelta with ⟨hk, hLower, hUpper⟩
    refine ⟨6 * k + 3, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨3 * k + 1, by omega⟩
    · exact ⟨2 * k + 1, by omega⟩
    · have hlower :
          p + 1 - (6 * k + 3) = p - 2 - 6 * k := by
        omega
      rw [hlower]
      exact hLower
    · have hupper :
          p + 1 + (6 * k + 3) = p + 4 + 6 * k := by
        omega
      rw [hupper]
      exact hUpper

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

/-!
## Direct-file verification summary

Running `lake env lean Delta/Conjecture.lean` prints these signatures after Lean
has elaborated and kernel-checked the finite-search bounds.
-/

#check Delta.KDeltaCondition.offset_lt_center
#check Delta.KDeltaCondition.k_lt_search_bound
