/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.LeftoverHash
public import QuantumFoundations.MinEntropy

/-!
# The leftover hash lemma in min-entropy form

Combines the classical leftover hash lemma (`leftover_hash_lemma`), stated via
the collision probability `∑ₓ p(x)²`, with the guessing probability
`guessProb p = maxₓ p(x)`. Since `∑ₓ p(x)² ≤ (maxₓ p x)·∑ₓ p(x) = guessProb p`
for a probability distribution, hashing `X ~ p` with a seed `h` drawn uniformly
from a 2-universal family, independently of `X`, gives

  `hashStatDist F p ≤ ½·√(|Y|·guessProb p) = ½·2^{(log₂|Y| − H_min(p))/2}`,

where `hashStatDist F p` is the statistical distance of `(h, h(X))` from
`(h, U_Y)`.

This is unconditional seeded extraction from a classical source: there is no
side-information register. Security against an adversary holding (classical or
quantum) side information about `X` needs the conditional leftover hash lemma,
stated with conditional min-entropy, which is not proved here.
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

/-- **Leftover hash lemma in min-entropy form.** For a probability distribution
`p`, the pair `(h, h(X))`, with `h` uniform over a 2-universal family and
`X ~ p` independent of `h`, is within statistical distance `½·√(|Y|·guessProb p)` of `(h, U_Y)`,
i.e. `½·2^{(log₂|Y| − H_min(p))/2}`. No side information is modelled. -/
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
