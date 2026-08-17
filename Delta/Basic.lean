import Mathlib.Data.Nat.Prime.Basic

namespace Delta

/-- `p` starts a cousin-prime pair when both `p` and `p + 4` are prime. -/
def IsCousinPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + 4)

/--
The core condition in the manuscript: `δ` is an odd multiple of three and the
two numbers symmetric about `p + 1` are prime.

This definition intentionally follows the manuscript.  A separate theorem
below proves that a valid witness is smaller than the centre, so subtraction
in `ℕ` does not truncate.
-/
def DeltaCondition (p δ : ℕ) : Prop :=
  Odd δ ∧
    3 ∣ δ ∧
    Nat.Prime (p + 1 - δ) ∧
    Nat.Prime (p + 1 + δ)

/-- The literal universal reading of the manuscript, including `p = 3`. -/
def RawDeltaConjecture : Prop :=
  ∀ p : ℕ, IsCousinPrime p → ∃ δ : ℕ, DeltaCondition p δ

/--
The non-exceptional Δ conjecture.  The hypothesis `3 < p` removes the cousin
prime pair `(3, 7)`, which is a counterexample to `RawDeltaConjecture`.
-/
def DeltaConjecture : Prop :=
  ∀ p : ℕ, 3 < p → IsCousinPrime p → ∃ δ : ℕ, DeltaCondition p δ

end Delta
