import Mathlib.Data.Nat.Prime.Basic

#check Nat.Prime

example : Nat.Prime 5 := by
  decide

example : Nat.Prime 5 ∧ Nat.Prime 11 := by
  decide
