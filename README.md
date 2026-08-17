# lean-delta

Lean 4 formalization of the Δ condition from *表哥質數對的結構性子猜想*.

## Statement tracked by the project

For a cousin-prime pair `p, p + 4`, a Δ witness is an odd multiple of three
such that both numbers symmetric about `p + 1` are prime:

```text
Nat.Prime (p + 1 - δ)  and  Nat.Prime (p + 1 + δ).
```

The literal universal statement has the exceptional counterexample `p = 3`:
the pair `(3, 7)` has no Δ witness.  The project's corrected conjecture therefore
assumes `3 < p`.

## Kernel-checked results

- A valid witness satisfies `δ < p + 1`; natural-number subtraction cannot truncate.
- The symmetric primes sum to `2 * p + 2`.
- For `3 < p`, a cousin-prime start is `1 mod 3` and its centre is `2 mod 3`.
- Adding or subtracting a Δ offset preserves the centre's residue modulo three.
- The manuscript's offsets `[3, 21, 27, 15, 45, 39, 9, 33]` cover all relevant
  cousin-prime starts below `877`, but fail at the cousin-prime pair `(877, 881)`.
  The offset `51` supplies a witness there: `(827, 929)`.
- An exhaustive `native_decide` proof verifies the corrected Δ conjecture for every
  cousin-prime start `p < 1,000,000`.

The last item is finite computational evidence checked by the Lean kernel.  It is
not a proof of the unbounded conjecture or of the manuscript's EH-based claim.

## Build

```bash
lake build
```

The main modules are:

- `Delta.Basic`: definitions;
- `Delta.Conjecture`: structural lemmas and the `p = 3` exception;
- `Delta.Residues`: modulo-three proofs;
- `Delta.FiniteVerification`: fixed-offset and exhaustive finite checks.
