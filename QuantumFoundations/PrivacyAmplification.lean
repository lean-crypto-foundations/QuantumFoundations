/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.LeftoverHash
public import QuantumFoundations.MinEntropy

/-!
# Privacy amplification in min-entropy form

Bridges the two pieces already proved:

* the classical Leftover Hash Lemma (`leftover_hash_lemma`), stated via the
  collision probability `∑ₓ p(x)²`, and
* conditional min-entropy in guessing-probability form (`guessProb`, `minEntropy`).

Since `collisionProb p = ∑ₓ p(x)² ≤ (maxₓ p x)·∑ₓ p(x) = guessProb p` for a
distribution, the leftover-hash bound becomes the standard **privacy-amplification
bound in min-entropy form**:

  `hashStatDist F p ≤ ½·√(|Y|·guessProb p) = ½·2^{(log₂|Y| − H_min(p))/2}`.

This is exactly the sender-privacy ε of BBCS quantum OT: hashing a string of
min-entropy `H_min` down to `ℓ = log₂|Y|` bits leaves the output within
`½·2^{−(H_min−ℓ)/2}` of uniform, hiding the un-chosen message.
-/

@[expose] public section

set_option autoImplicit false

namespace Quantum

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X]

/-- For a probability distribution, the collision probability is at most the
guessing probability: `∑ₓ p(x)² ≤ maxₓ p(x)`. -/
theorem collisionProb_le_guessProb {p : X → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) : collisionProb p ≤ guessProb p := by
  unfold collisionProb
  calc ∑ x, (p x) ^ 2
      ≤ ∑ x, guessProb p * p x := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_right (le_guessProb p x) (hp x)
    _ = guessProb p * ∑ x, p x := by rw [← Finset.mul_sum]
    _ = guessProb p := by rw [hsum, mul_one]

/-- **Privacy amplification (leftover hash in min-entropy form).** The output of
a 2-universal hash applied to a distribution `p` is within `½·√(|Y|·guessProb p)`
of uniform — i.e. `½·2^{(log₂|Y| − H_min(p))/2}`. This is the BBCS sender-privacy
bound: the un-chosen message is hidden up to this ε. -/
theorem leftover_hash_guessProb_bound (F : TwoUniversalHashFamily X Y)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    hashStatDist F p ≤ (1 / 2) * Real.sqrt ((Fintype.card Y : ℝ) * guessProb p) := by
  classical
  refine le_trans (leftover_hash_lemma F p hp hsum) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Real.sqrt_le_sqrt ?_
  exact mul_le_mul_of_nonneg_left (collisionProb_le_guessProb hp hsum)
    (Nat.cast_nonneg _)

end Quantum
