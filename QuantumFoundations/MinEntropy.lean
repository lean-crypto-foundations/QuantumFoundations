/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Min-Entropy (Classical Guessing-Probability Form)

This file develops the *classical* min-entropy of a finite probability vector in
its guessing-probability form, the foundation for the BB84/QKD min-entropy
accounting used downstream.

For a (sub-)distribution `p : ι → ℝ` over a nonempty finite index type `ι`, the
**guessing probability** is the largest single-outcome probability

  `guessProb p = max_x p x`,

and the **min-entropy** is

  `Hₘᵢₙ(p) = - log₂ (guessProb p)`.

Operationally, `guessProb p` is the success probability of the optimal strategy
that simply guesses the most likely outcome, and `Hₘᵢₙ` measures the number of
bits of uniform randomness in `p` from the adversary's worst-case (i.e. best-
guess) viewpoint.

Since `Real.log 0 = 0`, the zero vector gets `minEntropy 0 = - log₂ 0 = 0`
(`minEntropy_zero`), not the value `+∞` of the extended-real convention. Results
that use `Real.logb` algebraically, such as additivity over products, therefore
assume a strictly positive guessing probability.

## Main definitions

* `guessProb p` — the maximum entry `max_x p x` (via `Finset.sup'`).
* `minEntropy p` — `- Real.logb 2 (guessProb p)`.

## Main results

* `guessProb_le_one` — for a sub-distribution (`p x ≤ 1`), `guessProb p ≤ 1`.
* `minEntropy_nonneg` — `Hₘᵢₙ ≥ 0` when `0 < guessProb p ≤ 1`.
* `minEntropy_zero` — the zero vector has `Hₘᵢₙ = 0` under this real-valued
  convention.
* `guessProb_const` — `guessProb` of a constant vector is that constant.
* `minEntropy_uniform_two` — the uniform two-point distribution `fun _ => 1/2`
  has `Hₘᵢₙ = 1` (one bit).

The conjugate-basis measurement of BB84 gives the uniform two-point distribution, so
`minEntropy_uniform_two` is its single-qubit base case.

## References

* Renner, R. — *Security of Quantum Key Distribution*, PhD thesis, ETH 2005.
* König, Renner, Schaffner — *The operational meaning of min- and max-entropy*,
  IEEE Trans. Inf. Theory 2009.
-/

@[expose] public section

open scoped ENNReal

namespace Quantum

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Guessing probability** of a finite (sub-)probability vector `p : ι → ℝ`:
the maximum single-outcome probability `max_x p x`. This is the success
probability of the optimal "guess the most likely outcome" strategy. -/
def guessProb (p : ι → ℝ) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty p

/-- Every entry is `≤` the guessing probability. -/
theorem le_guessProb (p : ι → ℝ) (x : ι) : p x ≤ guessProb p :=
  Finset.le_sup' (s := Finset.univ) p (Finset.mem_univ x)

/-- The guessing probability is attained at some outcome. -/
theorem guessProb_mem_range (p : ι → ℝ) : ∃ x, guessProb p = p x := by
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) p
  exact ⟨x, hx⟩

/-- For a sub-distribution (`p x ≤ 1` for all `x`), the guessing probability is
`≤ 1`. -/
theorem guessProb_le_one {p : ι → ℝ} (h : ∀ x, p x ≤ 1) : guessProb p ≤ 1 :=
  Finset.sup'_le _ _ (fun x _ => h x)

/-- If every entry is nonnegative, so is the guessing probability. -/
theorem guessProb_nonneg {p : ι → ℝ} (h : ∀ x, 0 ≤ p x) : 0 ≤ guessProb p := by
  obtain ⟨x⟩ := (inferInstance : Nonempty ι)
  exact le_trans (h x) (le_guessProb p x)

/-- The guessing probability of a constant vector is that constant. -/
@[simp]
theorem guessProb_const (c : ℝ) : guessProb (fun _ : ι => c) = c := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun _ _ => le_refl c)
  · obtain ⟨x⟩ := (inferInstance : Nonempty ι)
    exact le_guessProb (fun _ : ι => c) x

/-- **Min-entropy** (classical guessing-probability form):
`Hₘᵢₙ(p) = - log₂ (guessProb p)`. This is real-valued: when `guessProb p = 0` it is
`- Real.logb 2 0 = 0` rather than `+∞`. -/
def minEntropy (p : ι → ℝ) : ℝ :=
  - Real.logb 2 (guessProb p)

/-- For a (sub-)distribution with positive guessing probability that is `≤ 1`,
the min-entropy is nonnegative. -/
theorem minEntropy_nonneg {p : ι → ℝ} (hpos : 0 < guessProb p)
    (hle : guessProb p ≤ 1) : 0 ≤ minEntropy p := by
  unfold minEntropy
  rw [neg_nonneg]
  exact Real.logb_nonpos (by norm_num) (le_of_lt hpos) hle

/-- Min-entropy of a constant `c` vector is `- log₂ c`. -/
@[simp]
theorem minEntropy_const (c : ℝ) : minEntropy (fun _ : ι => c) = - Real.logb 2 c := by
  unfold minEntropy
  rw [guessProb_const]

/-- The zero vector has min-entropy `0`, because `Real.logb 2 0 = 0`; the
extended-real convention would give `+∞`. -/
@[simp]
theorem minEntropy_zero : minEntropy (0 : ι → ℝ) = 0 := by
  have h := minEntropy_const (ι := ι) 0
  rw [Real.logb_zero, neg_zero] at h
  exact h

end

/-! ## Uniform two-point distribution -/

/-- The uniform distribution on two outcomes: `fun _ : Fin 2 => 1/2`. Its
guessing probability is `1/2`. -/
theorem guessProb_uniform_two : guessProb (fun _ : Fin 2 => (1 : ℝ) / 2) = 1 / 2 :=
  guessProb_const (1 / 2)

/-- **The uniform two-point distribution has min-entropy 1** (one bit):
`Hₘᵢₙ(1/2, 1/2) = - log₂(1/2) = 1`. -/
theorem minEntropy_uniform_two : minEntropy (fun _ : Fin 2 => (1 : ℝ) / 2) = 1 := by
  rw [minEntropy_const]
  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.logb_inv, neg_neg,
    Real.logb_self_eq_one (by norm_num)]

end Quantum
