import Delta.Conjecture
import Mathlib.Data.Nat.ModEq

namespace Delta

namespace IsCousinPrime

/-- Away from the exceptional prime `3`, a cousin-prime start is `1 mod 3`. -/
theorem start_mod_three {p : ℕ} (hp3 : 3 < p) (h : IsCousinPrime p) : p % 3 = 1 := by
  have hp : Nat.Prime p := h.1
  have hp4 : Nat.Prime (p + 4) := h.2
  have hmod_ne_zero : p % 3 ≠ 0 := by
    intro hzero
    have hdiv : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hzero
    have hp_eq : p = 3 := (hp.dvd_iff_eq (by norm_num)).mp hdiv
    omega
  have hmod_ne_two : p % 3 ≠ 2 := by
    intro htwo
    have hzero : (p + 4) % 3 = 0 := by
      omega
    have hdiv : 3 ∣ p + 4 := Nat.dvd_iff_mod_eq_zero.mpr hzero
    have hp4_eq : p + 4 = 3 := (hp4.dvd_iff_eq (by norm_num)).mp hdiv
    omega
  have hlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  omega

/-- The centre `p + 1` of a non-exceptional cousin-prime pair is `2 mod 3`. -/
theorem center_mod_three {p : ℕ} (hp3 : 3 < p) (h : IsCousinPrime p) :
    (p + 1) % 3 = 2 := by
  rw [Nat.add_mod, start_mod_three hp3 h]

end IsCousinPrime

namespace DeltaCondition

/-- Every Δ offset is congruent to `3` modulo `6`. -/
theorem delta_mod_six {p δ : ℕ} (h : DeltaCondition p δ) : δ % 6 = 3 := by
  have hOdd : Odd δ := h.1
  obtain ⟨k, hk⟩ := h.2.1
  subst δ
  have hkOdd : Odd k := Nat.Odd.of_mul_right hOdd
  obtain ⟨m, hm⟩ := hkOdd
  omega

/-- Subtracting a Δ offset preserves the centre's residue modulo three. -/
theorem lower_modEq_center {p δ : ℕ} (h : DeltaCondition p δ) :
    p + 1 - δ ≡ p + 1 [MOD 3] := by
  have hδ : δ ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.mpr h.2.1
  simpa using Nat.ModEq.sub (Nat.le_of_lt h.lt_center) (Nat.zero_le (p + 1))
    (Nat.ModEq.rfl) hδ

/-- Adding a Δ offset preserves the centre's residue modulo three. -/
theorem upper_modEq_center {p δ : ℕ} (h : DeltaCondition p δ) :
    p + 1 + δ ≡ p + 1 [MOD 3] := by
  have hδ : δ ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.mpr h.2.1
  simpa using (Nat.ModEq.rfl.add hδ : p + 1 + δ ≡ p + 1 + 0 [MOD 3])

/-- Both primes produced by a non-exceptional Δ witness are `2 mod 3`. -/
theorem prime_pair_mod_three {p δ : ℕ} (hp3 : 3 < p) (hp : IsCousinPrime p)
    (hδ : DeltaCondition p δ) :
    (p + 1 - δ) % 3 = 2 ∧ (p + 1 + δ) % 3 = 2 := by
  have hcenter : p + 1 ≡ 2 [MOD 3] := by
    simpa [Nat.ModEq] using IsCousinPrime.center_mod_three hp3 hp
  constructor
  · exact hδ.lower_modEq_center.trans hcenter
  · exact hδ.upper_modEq_center.trans hcenter

end DeltaCondition

end Delta
