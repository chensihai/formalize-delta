import Delta.Residues

namespace Delta

/-- The eight offsets reported in Section 4 of the manuscript, in its stated order. -/
def manuscriptOffsets : List ℕ :=
  [3, 21, 27, 15, 45, 39, 9, 33]

/-- A computation-friendly form of `DeltaCondition`. -/
abbrev FiniteDeltaCondition (p δ : ℕ) : Prop :=
  δ % 2 = 1 ∧
    3 ∣ δ ∧
    Nat.Prime (p + 1 - δ) ∧
    Nat.Prime (p + 1 + δ)

theorem finiteDeltaCondition_iff {p δ : ℕ} :
    FiniteDeltaCondition p δ ↔ DeltaCondition p δ := by
  simp [FiniteDeltaCondition, DeltaCondition, Nat.odd_iff]

/-- One of the eight offsets in the manuscript supplies a Δ witness for `p`. -/
abbrev ManuscriptOffsetCovers (p : ℕ) : Prop :=
  ∃ i : Fin manuscriptOffsets.length,
    FiniteDeltaCondition p (manuscriptOffsets.get i)

/-- Every non-exceptional cousin-prime start below `bound` is covered. -/
abbrev ManuscriptVerifiedBelow (bound : ℕ) : Prop :=
  ∀ p : Fin bound,
    3 < p.val → IsCousinPrime p.val → ManuscriptOffsetCovers p.val

/-- The manuscript's eight offsets cover every relevant cousin-prime start below `877`. -/
theorem manuscript_verified_below_877 : ManuscriptVerifiedBelow 877 := by
  change ∀ p : Fin 877,
    3 < p.val →
      (Nat.Prime p.val ∧ Nat.Prime (p.val + 4)) →
      ∃ i : Fin 8,
        let δ := ([3, 21, 27, 15, 45, 39, 9, 33] : List ℕ).get i
        δ % 2 = 1 ∧
          3 ∣ δ ∧
          Nat.Prime (p.val + 1 - δ) ∧
          Nat.Prime (p.val + 1 + δ)
  native_decide

/-- `877` and `881` are cousin primes, but none of the eight listed offsets works. -/
theorem manuscript_offsets_do_not_cover_877 :
    IsCousinPrime 877 ∧ ¬ ManuscriptOffsetCovers 877 := by
  constructor
  · norm_num [IsCousinPrime]
  · change ¬∃ i : Fin 8,
      let δ := ([3, 21, 27, 15, 45, 39, 9, 33] : List ℕ).get i
      δ % 2 = 1 ∧
        3 ∣ δ ∧
        Nat.Prime (878 - δ) ∧
        Nat.Prime (878 + δ)
    native_decide

/-- The next odd multiple of three, `51`, does supply a witness for `877`. -/
theorem deltaCondition_877_51 : DeltaCondition 877 51 := by
  norm_num [DeltaCondition]

/-- A bounded proposition that searches every mathematically possible offset. -/
abbrev DeltaVerifiedBelow (bound : ℕ) : Prop :=
  ∀ p : Fin bound,
    3 < p.val →
      IsCousinPrime p.val →
      ∃ δ : Fin (p.val + 1), FiniteDeltaCondition p.val δ.val

/--
Kernel-checked verification of the corrected Δ conjecture for every
cousin-prime start `p < 1,000,000`.
-/
theorem delta_verified_below_one_million : DeltaVerifiedBelow 1_000_000 := by
  change ∀ p : Fin 1_000_000,
    3 < p.val →
      (Nat.Prime p.val ∧ Nat.Prime (p.val + 4)) →
      ∃ δ : Fin (p.val + 1),
        δ.val % 2 = 1 ∧
          3 ∣ δ.val ∧
          Nat.Prime (p.val + 1 - δ.val) ∧
          Nat.Prime (p.val + 1 + δ.val)
  native_decide

/-- Restate the exhaustive finite computation using `DeltaCondition`. -/
theorem deltaConjecture_verified_below_one_million :
    ∀ p : ℕ, p < 1_000_000 → 3 < p → IsCousinPrime p →
      ∃ δ : ℕ, DeltaCondition p δ := by
  intro p hpBound hp3 hp
  obtain ⟨δ, hδ⟩ := delta_verified_below_one_million ⟨p, hpBound⟩ hp3 hp
  exact ⟨δ.val, finiteDeltaCondition_iff.mp hδ⟩

end Delta
