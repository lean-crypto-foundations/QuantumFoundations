/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The trace against a Hermitian matrix in its eigenbasis

A Mathlib candidate, next to the spectral theorem in `Mathlib/Analysis/Matrix/Spectrum.lean`.

## Main results

* `Matrix.IsHermitian.trace_mul_eq_sum_eigenvalues` — for a Hermitian matrix `X` with
  eigenvector unitary `U`, `tr(E X) = ∑ i, (U* E U) i i * λᵢ`.
-/

@[expose] public section

set_option autoImplicit false

open Matrix

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace `tr(E X)` in the eigenbasis of the Hermitian matrix `X`: the sum of the
diagonal entries of `U* E U` times the eigenvalues of `X`, for the eigenvector unitary `U` of
`X`. -/
theorem trace_mul_eq_sum_eigenvalues {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (E : Matrix n n ℂ) :
    (E * X).trace = ∑ i, (star (hX.eigenvectorUnitary : Matrix n n ℂ) * E *
      (hX.eigenvectorUnitary : Matrix n n ℂ)) i i *
      (↑(hX.eigenvalues i) : ℂ) := by
  set U := (hX.eigenvectorUnitary : Matrix n n ℂ)
  set D := diagonal (RCLike.ofReal ∘ hX.eigenvalues : n → ℂ)
  have hX_spec : X = U * D * star U := by
    rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
  calc (E * X).trace
      = (E * (U * D * star U)).trace := by rw [hX_spec]
    _ = ((E * U) * D * star U).trace := by
        congr 1; rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (star U * (E * U) * D).trace := by rw [trace_mul_cycle]
    _ = (star U * E * U * D).trace := by
        congr 1; rw [← Matrix.mul_assoc (star U)]
    _ = ∑ i, (star U * E * U) i i * (↑(hX.eigenvalues i) : ℂ) := by
        simp only [Matrix.trace, Matrix.diag]
        congr 1; funext i; rw [mul_diagonal]; simp [Function.comp]

end Matrix.IsHermitian
