/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.MinEntropy

/-!
# Additivity of min-entropy over independent registers

For two independent (sub-)probability vectors `p₀ : ι₀ → ℝ` and `p₁ : ι₁ → ℝ`,
the guessing probability of the product distribution factors:

  `guessProb (fun (x,y) => p₀ x * p₁ y) = guessProb p₀ * guessProb p₁`,

so, when both guessing probabilities are positive, the min-entropy is **additive**:

  `Hₘᵢₙ(p₀ ⊗ p₁) = Hₘᵢₙ(p₀) + Hₘᵢₙ(p₁)`.

(With the convention `minEntropy 0 = 0` this fails for a zero factor.)

Iterating this gives the min-entropy of `n` *independent* conjugate-basis BB84
measurements: each contributes `1` bit (`minEntropy_uniform_two`), so the
joint min-entropy of the independent case is `n`. This covers independent registers only.
The DFRSS uncertainty relation (full version, Corollary 3.4: `H_∞^ε(X|Θ) ≥ (½−2λ)n`), which
holds for adversarially prepared states, is not formalized here.
-/

@[expose] public section

set_option autoImplicit false

namespace Quantum

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Guessing probability factors over independent registers.** For the product
distribution `(x,y) ↦ p₀ x · p₁ y` of two nonnegative vectors, the maximum-entry
probability is the product of the per-register maxima. -/
theorem guessProb_product {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    [Nonempty ι₀] [Nonempty ι₁] (p₀ : ι₀ → ℝ) (p₁ : ι₁ → ℝ)
    (h₀ : ∀ x, 0 ≤ p₀ x) (h₁ : ∀ y, 0 ≤ p₁ y) :
    guessProb (fun q : ι₀ × ι₁ => p₀ q.1 * p₁ q.2)
      = guessProb p₀ * guessProb p₁ := by
  apply le_antisymm
  · -- every product entry is ≤ the product of the maxima
    refine Finset.sup'_le _ _ ?_
    intro q _
    exact mul_le_mul (le_guessProb p₀ q.1) (le_guessProb p₁ q.2)
      (h₁ q.2) (guessProb_nonneg h₀)
  · -- the (argmax, argmax) pair achieves the product of the maxima
    obtain ⟨x, _, hx⟩ :=
      Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι₀)) p₀
    obtain ⟨y, _, hy⟩ :=
      Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι₁)) p₁
    have hxy : guessProb p₀ * guessProb p₁
        = (fun q : ι₀ × ι₁ => p₀ q.1 * p₁ q.2) (x, y) := by
      simp only [guessProb]
      rw [hx, hy]
    rw [hxy]
    exact le_guessProb (fun q : ι₀ × ι₁ => p₀ q.1 * p₁ q.2) (x, y)

/-- **Min-entropy is additive over independent registers.** The positivity
hypotheses exclude a zero factor: `minEntropy` of the zero vector is `0`
(`minEntropy_zero`), so additivity fails there. -/
theorem minEntropy_product {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    [Nonempty ι₀] [Nonempty ι₁] (p₀ : ι₀ → ℝ) (p₁ : ι₁ → ℝ)
    (h₀ : ∀ x, 0 ≤ p₀ x) (h₁ : ∀ y, 0 ≤ p₁ y)
    (hp₀ : 0 < guessProb p₀) (hp₁ : 0 < guessProb p₁) :
    minEntropy (fun q : ι₀ × ι₁ => p₀ q.1 * p₁ q.2)
      = minEntropy p₀ + minEntropy p₁ := by
  unfold minEntropy
  rw [guessProb_product p₀ p₁ h₀ h₁,
    Real.logb_mul (ne_of_gt hp₀) (ne_of_gt hp₁)]
  ring

end Quantum
