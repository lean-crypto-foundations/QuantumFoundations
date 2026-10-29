/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.TraceNorm
public import QuantumFoundations.CPMap

/-!
# Triangle inequality and channel contraction of the trace norm

Over a finite index type `n`, this file proves the dual bound of the trace norm of a
Hermitian matrix by Hermitian contractions `-1 ≤ S ≤ 1`, and derives from it the
triangle inequality of `traceNormH` and its contraction under CPTP maps.

## Main definitions

* `IsHermContraction` — a matrix `S` with `1 - S` and `1 + S` positive semidefinite

## Main results

* `trace_mul_re_le_traceNormH` — `Re tr(S X) ≤ ‖X‖₁` for a contraction `S` and
  Hermitian `X`
* `traceNormH_add_le` — `‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁` for Hermitian `A`, `B`
* `traceNormH_map_le` — `‖Φ X‖₁ ≤ ‖X‖₁` for a CPTP map `Φ` and Hermitian `X`
* `traceDist_map_le` — `traceDist (Φ ρ) (Φ σ) ≤ traceDist ρ σ`
-/

@[expose] public section

open scoped Matrix ComplexOrder
open Matrix

namespace Quantum

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Hermitian contraction: `-1 ≤ S ≤ 1` in the Loewner order. -/
def IsHermContraction (S : Matrix n n ℂ) : Prop :=
  (1 - S).PosSemidef ∧ (1 + S).PosSemidef

/-- Unitary conjugation preserves Hermitian contractions. -/
theorem IsHermContraction.conj {S : Matrix n n ℂ} (hS : IsHermContraction S)
    (U : ↥(unitaryGroup n ℂ)) :
    IsHermContraction (star (U : Matrix n n ℂ) * S * (U : Matrix n n ℂ)) := by
  constructor
  · have h : 1 - star (U : Matrix n n ℂ) * S * (U : Matrix n n ℂ) =
        star (U : Matrix n n ℂ) * (1 - S) * (U : Matrix n n ℂ) := by
      rw [mul_sub, sub_mul, mul_one, UnitaryGroup.star_mul_self]
    rw [h, star_eq_conjTranspose]
    exact hS.1.conjTranspose_mul_mul_same _
  · have h : 1 + star (U : Matrix n n ℂ) * S * (U : Matrix n n ℂ) =
        star (U : Matrix n n ℂ) * (1 + S) * (U : Matrix n n ℂ) := by
      rw [mul_add, add_mul, mul_one, UnitaryGroup.star_mul_self]
    rw [h, star_eq_conjTranspose]
    exact hS.2.conjTranspose_mul_mul_same _

omit [Fintype n] in
/-- The diagonal entries of a Hermitian contraction have real part in `[-1, 1]`. -/
theorem IsHermContraction.diag_re_mem {S : Matrix n n ℂ} (hS : IsHermContraction S)
    (i : n) : -1 ≤ (S i i).re ∧ (S i i).re ≤ 1 := by
  constructor
  · have h := (Complex.nonneg_iff.mp (hS.2.diag_nonneg (i := i))).1
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Complex.add_re, Complex.one_re] at h
    linarith
  · have h := (Complex.nonneg_iff.mp (hS.1.diag_nonneg (i := i))).1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re] at h
    linarith

/-- A self-adjoint involution is a Hermitian contraction. -/
theorem isHermContraction_of_involution {S : Matrix n n ℂ} (hSh : Sᴴ = S)
    (hSS : S * S = 1) : IsHermContraction S := by
  have h1 : 1 - S = (1 / 2 : ℂ) • ((1 - S)ᴴ * (1 - S)) := by
    simp only [conjTranspose_sub, conjTranspose_one, hSh, sub_mul, mul_sub, hSS, one_mul,
      mul_one]
    module
  have h2 : 1 + S = (1 / 2 : ℂ) • ((1 + S)ᴴ * (1 + S)) := by
    simp only [conjTranspose_add, conjTranspose_one, hSh, add_mul, mul_add, hSS, one_mul,
      mul_one]
    module
  constructor
  · rw [h1]; exact (posSemidef_conjTranspose_mul_self _).smul (by positivity)
  · rw [h2]; exact (posSemidef_conjTranspose_mul_self _).smul (by positivity)

omit [Fintype n] in
/-- A positive unital map sends Hermitian contractions to Hermitian contractions. -/
theorem IsHermContraction.map {Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΨ : IsPositiveMap Ψ) (hΨ1 : Ψ 1 = 1) {S : Matrix n n ℂ}
    (hS : IsHermContraction S) : IsHermContraction (Ψ S) := by
  constructor
  · rw [← hΨ1, ← map_sub]; exact hΨ _ hS.1
  · rw [← hΨ1, ← map_add]; exact hΨ _ hS.2

/-- The trace `tr(S X)` in the eigenbasis of the Hermitian matrix `X`. -/
theorem trace_mul_eq_sum_eigenvalues (S X : Matrix n n ℂ) (hX : X.IsHermitian) :
    (S * X).trace = ∑ i, (star (hX.eigenvectorUnitary : Matrix n n ℂ) * S *
      (hX.eigenvectorUnitary : Matrix n n ℂ)) i i * (↑(hX.eigenvalues i) : ℂ) := by
  set U := (hX.eigenvectorUnitary : Matrix n n ℂ)
  set D := diagonal (RCLike.ofReal ∘ hX.eigenvalues : n → ℂ)
  have hX_spec : X = U * D * star U := by
    rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
  calc (S * X).trace
      = (S * (U * D * star U)).trace := by rw [hX_spec]
    _ = ((S * U) * D * star U).trace := by
        congr 1; rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (star U * (S * U) * D).trace := by rw [trace_mul_cycle]
    _ = (star U * S * U * D).trace := by
        congr 1; rw [← Matrix.mul_assoc (star U)]
    _ = ∑ i, (star U * S * U) i i * (↑(hX.eigenvalues i) : ℂ) := by
        simp only [Matrix.trace, Matrix.diag]
        congr 1; funext i; rw [mul_diagonal]; simp [Function.comp]

/-- Dual bound of the trace norm: `Re tr(S X) ≤ ‖X‖₁` for a Hermitian contraction `S`
and a Hermitian matrix `X`. -/
theorem trace_mul_re_le_traceNormH (X : Matrix n n ℂ) (hX : X.IsHermitian)
    {S : Matrix n n ℂ} (hS : IsHermContraction S) :
    (S * X).trace.re ≤ traceNormH X hX := by
  rw [trace_mul_eq_sum_eigenvalues S X hX, Complex.re_sum]
  simp_rw [Complex.re_mul_ofReal]
  refine Finset.sum_le_sum fun i _ => ?_
  have ⟨h1, h2⟩ := (hS.conj hX.eigenvectorUnitary).diag_re_mem i
  rcases le_total 0 (hX.eigenvalues i) with h | h <;>
    [rw [abs_of_nonneg h]; rw [abs_of_nonpos h]] <;> nlinarith

/-- Triangle inequality of the trace norm of Hermitian matrices. -/
theorem traceNormH_add_le (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (A + B).IsHermitian) :
    traceNormH (A + B) hAB ≤ traceNormH A hA + traceNormH B hB := by
  obtain ⟨S, hSh, hSS, hS⟩ := exists_selfAdjoint_involution_trace_eq_traceNormH (A + B) hAB
  have hc := isHermContraction_of_involution hSh hSS
  rw [← hS, mul_add, trace_add, Complex.add_re]
  exact add_le_add (trace_mul_re_le_traceNormH A hA hc) (trace_mul_re_le_traceNormH B hB hc)

/-- A CPTP map does not increase the trace norm of a Hermitian matrix. -/
theorem traceNormH_map_le (Φ : CPTPMap n) (X : Matrix n n ℂ) (hX : X.IsHermitian)
    (hΦX : (Φ.toLinearMap X).IsHermitian) :
    traceNormH (Φ.toLinearMap X) hΦX ≤ traceNormH X hX := by
  obtain ⟨S, hSh, hSS, hS⟩ :=
    exists_selfAdjoint_involution_trace_eq_traceNormH (Φ.toLinearMap X) hΦX
  have hc := isHermContraction_of_involution hSh hSS
  obtain ⟨hpos, hunit⟩ := cptp_dual_is_cpu Φ
  rw [← hS, ← dual_spec]
  exact trace_mul_re_le_traceNormH X hX (hc.map hpos hunit)

/-- Trace distance contracts under CPTP maps. -/
theorem traceDist_map_le (Φ : CPTPMap n) {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (h : (ρ - σ).IsHermitian) (hΦρ : (Φ.toLinearMap ρ).PosSemidef)
    (hΦσ : (Φ.toLinearMap σ).PosSemidef)
    (hΦ : (Φ.toLinearMap ρ - Φ.toLinearMap σ).IsHermitian) :
    traceDist (Φ.toLinearMap ρ) (Φ.toLinearMap σ) hΦρ hΦσ hΦ ≤ traceDist ρ σ hρ hσ h := by
  have hΦ' : (Φ.toLinearMap (ρ - σ)).IsHermitian := by rwa [map_sub]
  have key := traceNormH_map_le Φ (ρ - σ) h hΦ'
  have heq : traceNormH (Φ.toLinearMap ρ - Φ.toLinearMap σ) hΦ =
      traceNormH (Φ.toLinearMap (ρ - σ)) hΦ' := by
    congr 1; rw [map_sub]
  unfold traceDist
  rw [heq]
  linarith

end Quantum
