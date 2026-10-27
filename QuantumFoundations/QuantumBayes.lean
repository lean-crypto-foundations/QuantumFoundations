/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.Instrument
public import QuantumFoundations.CPMap
public import QuantumFoundations.PetzRecovery

/-!
# Quantum Bayesian Inversion

The Bayes equation for the Petz recovery map, and the Lüders (Jeffrey) update
of a density matrix by a measurement effect.

## Mathematical Background

In an effectus (Cho-Jacobs 2015), Bayesian inversion for a channel Φ w.r.t.
a prior σ is defined by the equation:

```
Φ†_σ(A) = σ^{1/2} Φ†[Φ(σ)^{-1/2} A Φ(σ)^{-1/2}] σ^{1/2}
```

This is exactly the Petz recovery map. Properties:
1. `Φ†_σ(Φ(σ)) = σ` (exact recovery of the prior)
2. Compositionality: `(Ψ∘Φ)†_σ = Φ†_σ ∘ Ψ†_{Φ(σ)}`
3. Uniqueness (Parzygnat-Buscemi 2023)

## Main Results

* `quantum_bayes_rule` — the defining equation of `petzRecovery`
* `jeffreyUpdate` — the Lüders update of a prior by a measurement effect
* `jeffreyUpdate_denominator` — the update normalizes by the Born
  probability `tr(E σ)`
* `jeffreyUpdate_density` — the update preserves positivity and unit trace

Exact recovery and the chain rule for the Petz map live in `PetzRecovery.lean`,
as the theorems `petzRecovery_exact` and `petzRecovery_comp`.

## References

* Cho, K. & Jacobs, B. — *Disintegration and Bayesian Inversion via
  String Diagrams*, MSCS 29(7), 2019
* Parzygnat, A.J. & Buscemi, F. — *Axioms for Retrodiction*, Quantum 7, 2023
* Leifer, M.S. — *Quantum Dynamics as an Analog of Conditional Probability*,
  PRA 74, 2006
-/

@[expose] public section

open scoped Matrix ComplexOrder ENNReal
open Matrix

noncomputable section

namespace Quantum.QuantumBayes

open Quantum

variable {d : ℕ}

-- Loewner order instances for CFC (inherited from PetzRecovery imports).
attribute [local instance] instPartialOrder Matrix.instStarOrderedRing
  Matrix.instNonnegSpectrumClass

/-! ## Helper lemmas for Jeffrey update -/

private lemma complex_inv_of_real_im_zero (z : ℂ) (h_im : z.im = 0) :
    z⁻¹ = Complex.ofReal (z.re⁻¹) := by
  have h_eq : z = Complex.ofReal z.re := by apply Complex.ext <;> simp [h_im]
  rw [h_eq, ← Complex.ofReal_inv]; simp [Complex.ofReal_re]

private lemma psd_smul_trace_inv (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef)
    (_h_ne : M.trace ≠ 0) :
    (M.trace⁻¹ • M).PosSemidef := by
  -- Trace of PSD is real (im = 0, re ≥ 0), so trace⁻¹ is a non-negative real.
  -- Rewrite the trace inverse via `complex_inv_of_real_im_zero` and then
  -- apply `hM.smul` with the ℂ-coercion of the real `0 ≤ trace.re⁻¹`.
  have h_im : M.trace.im = 0 := trace_im_zero_of_hermitian hM.isHermitian
  have h_re_nn : 0 ≤ M.trace.re := trace_re_nonneg_of_psd hM
  have h_inv_eq : M.trace⁻¹ = Complex.ofReal (M.trace.re⁻¹) :=
    complex_inv_of_real_im_zero M.trace h_im
  rw [h_inv_eq]
  exact hM.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr h_re_nn))

/-- The trace of the unnormalized Lüders update is the Born probability of the
    effect: `tr(E^{1/2} σ E^{1/2}) = tr(E σ)`. -/
theorem trace_sqrt_conj (σ : Matrix (Fin d) (Fin d) ℂ) (E : Matrix (Fin d) (Fin d) ℂ)
    (hE : E.PosSemidef) :
    (psdSqrt E hE * σ * psdSqrt E hE).trace = (E * σ).trace := by
  have : (psdSqrt E hE * σ * psdSqrt E hE).trace =
      (psdSqrt E hE * (psdSqrt E hE * σ)).trace := by
    rw [trace_mul_comm (psdSqrt E hE * σ) (psdSqrt E hE)]
  rw [this, ← mul_assoc, psdSqrt_mul_psdSqrt]

/-! ## Quantum Bayesian Inversion via Petz Map -/

/-- **Quantum Bayes' rule**: the defining equation of `petzRecovery`.

    For a channel Φ preserving positivity and a prior state σ,

    `R_{σ,Φ}(A) = σ^{1/2} Φ†[Φ(σ)^{-1/2} A Φ(σ)^{-1/2}] σ^{1/2}`

    where `Φ† = dualMap Φ` is the trace dual of `Φ`. -/
theorem quantum_bayes_rule
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hΦ : ∀ ρ, ρ.PosSemidef → (Φ ρ).PosSemidef)
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    petzRecovery σ hσ Φ hΦ A =
      psdSqrt σ hσ *
        dualMap Φ (psdInvSqrt (Φ σ) (hΦ σ hσ) * A *
          psdInvSqrt (Φ σ) (hΦ σ hσ)) *
        psdSqrt σ hσ :=
  rfl

/-! ## Jeffrey Update -/

/-- **Quantum Jeffrey update** (Lueders rule): updating a prior σ given
    evidence from a measurement with effect E.

    The updated state is:
    `σ_E = E^{1/2} σ E^{1/2} / tr(E^{1/2} σ E^{1/2})`

    where `E^{1/2}` is the matrix square root via `psdSqrt` (CFC). -/
def jeffreyUpdate (σ : Matrix (Fin d) (Fin d) ℂ) (E : Matrix (Fin d) (Fin d) ℂ)
    (hE : E.PosSemidef) (_h_le : (1 - E).PosSemidef) :
    Matrix (Fin d) (Fin d) ℂ :=
  let E_half := psdSqrt E hE
  let unnormalized := E_half * σ * E_half
  (unnormalized.trace)⁻¹ • unnormalized

/-- Jeffrey update preserves density matrices (PSD, trace 1). -/
theorem jeffreyUpdate_density
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef) (_hσ_tr : σ.trace = 1)
    (E : Matrix (Fin d) (Fin d) ℂ) (hE : E.PosSemidef) (h_le : (1 - E).PosSemidef)
    (h_nonzero : (E * σ).trace ≠ 0) :
    (jeffreyUpdate σ E hE h_le).PosSemidef ∧
    (jeffreyUpdate σ E hE h_le).trace = 1 := by
  unfold jeffreyUpdate
  simp only []
  have h_herm : (psdSqrt E hE)ᴴ = psdSqrt E hE := (psdSqrt_posSemidef E hE).1
  have h_unnorm_psd : (psdSqrt E hE * σ * psdSqrt E hE).PosSemidef := by
    rw [show psdSqrt E hE * σ * psdSqrt E hE =
          psdSqrt E hE * σ * (psdSqrt E hE)ᴴ from by rw [h_herm]]
    exact hσ.mul_mul_conjTranspose_same _
  have h_trace_ne : (psdSqrt E hE * σ * psdSqrt E hE).trace ≠ 0 := by
    rw [trace_sqrt_conj σ E hE]; exact h_nonzero
  exact ⟨psd_smul_trace_inv _ h_unnorm_psd h_trace_ne,
    by rw [Matrix.trace_smul]; exact inv_mul_cancel₀ h_trace_ne⟩

/-- The Jeffrey update divides by the Born probability of the effect:

    `σ_E = E^{1/2} σ E^{1/2} / tr(E σ)`

    This is the quantum form of the Bayes denominator `P(A)`. -/
theorem jeffreyUpdate_denominator
    (σ : Matrix (Fin d) (Fin d) ℂ) (E : Matrix (Fin d) (Fin d) ℂ)
    (hE : E.PosSemidef) (h_le : (1 - E).PosSemidef) :
    jeffreyUpdate σ E hE h_le =
      (E * σ).trace⁻¹ • (psdSqrt E hE * σ * psdSqrt E hE) := by
  unfold jeffreyUpdate
  simp only []
  rw [trace_sqrt_conj σ E hE]

end Quantum.QuantumBayes
