/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.CPMap

/-!
# Contraction of the trace norm and the trace distance

Over a finite index type `n`, a positive trace-nonincreasing linear map `Φ` on matrices
does not increase the trace norm of a Hermitian matrix nor the trace distance of two
positive semidefinite matrices. The proof bounds `‖Φ X‖₁ = Re tr(S Φ(X)) = Re tr(Φ†(S) X)`
for a self-adjoint involution `S` and uses that the trace dual `Φ†` is positive and
sub-unital, so that `Φ†(S)` is a Hermitian contraction. CPTP maps are the
trace-preserving special case.

## Main results

* `IsPositiveMap.isHermitian_map` — a positive map preserves Hermitian matrices
* `one_sub_dualMap_one_posSemidef` — `Φ†(1) ≤ 1` for a positive trace-nonincreasing `Φ`
* `traceNormH_map_le_of_isSTP` — `‖Φ X‖₁ ≤ ‖X‖₁` for positive trace-nonincreasing `Φ`
* `traceDist_map_le_of_isSTP` — `traceDist (Φ ρ) (Φ σ) ≤ traceDist ρ σ` for such `Φ`
* `traceNormH_map_le`, `traceDist_map_le` — the same for a CPTP map
-/

@[expose] public section

open scoped Matrix ComplexOrder
open Matrix

namespace Quantum

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- A positive map sends Hermitian matrices to Hermitian matrices. -/
theorem IsPositiveMap.isHermitian_map [Finite n] {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΦ : IsPositiveMap Φ) {X : Matrix n n ℂ} (hX : X.IsHermitian) : (Φ X).IsHermitian :=
  (hΦ.map_conjTranspose X).symm.trans (congrArg Φ hX)

omit [DecidableEq n] in
/-- A trace-preserving map is trace-nonincreasing. -/
theorem IsTP.isSTP {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hΦ : IsTP Φ) : IsSTP Φ :=
  fun A _ => (congrArg Complex.re (hΦ A)).le

/-- The trace dual of a positive trace-nonincreasing map is sub-unital:
`Φ†(1) ≤ 1` in the Loewner order. -/
theorem one_sub_dualMap_one_posSemidef {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΦ : IsPositiveMap Φ) (hT : IsSTP Φ) : (1 - dualMap Φ 1).PosSemidef := by
  have hD := dual_positive_of_positive Φ hΦ 1 PosSemidef.one
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_one.sub hD.isHermitian, fun x => ?_⟩
  set P := vecMulVec x (star x) with hPdef
  have hP : P.PosSemidef := by simpa using posSemidef_vecMulVec_star_self (star x)
  have hq : star x ⬝ᵥ (1 - dualMap Φ 1) *ᵥ x = P.trace - (Φ P).trace := by
    rw [show star x ⬝ᵥ (1 - dualMap Φ 1) *ᵥ x = ((1 - dualMap Φ 1) * P).trace by
      rw [hPdef, mul_vecMulVec, trace_vecMulVec, dotProduct_comm],
      sub_mul, trace_sub, one_mul, dual_spec, one_mul]
  have h1 := Complex.nonneg_iff.mp hP.trace_nonneg
  have h2 := Complex.nonneg_iff.mp (hΦ P hP).trace_nonneg
  have h3 := hT P hP
  rw [hq, Complex.nonneg_iff, Complex.sub_re, Complex.sub_im]
  exact ⟨by linarith, by linarith [h1.2, h2.2]⟩

omit [Fintype n] in
/-- A positive sub-unital map sends Hermitian contractions to Hermitian contractions. -/
theorem IsHermContraction.map {Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΨ : IsPositiveMap Ψ) (hΨ1 : (1 - Ψ 1).PosSemidef) {S : Matrix n n ℂ}
    (hS : IsHermContraction S) : IsHermContraction (Ψ S) := by
  constructor
  · have h : 1 - Ψ S = (1 - Ψ 1) + Ψ (1 - S) := by rw [map_sub]; abel
    rw [h]; exact hΨ1.add (hΨ _ hS.1)
  · have h : 1 + Ψ S = (1 - Ψ 1) + Ψ (1 + S) := by rw [map_add]; abel
    rw [h]; exact hΨ1.add (hΨ _ hS.2)

/-- A positive trace-nonincreasing map does not increase the trace norm of a Hermitian
matrix. -/
theorem traceNormH_map_le_of_isSTP {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΦ : IsPositiveMap Φ) (hT : IsSTP Φ) (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    traceNormH (Φ X) (hΦ.isHermitian_map hX) ≤ traceNormH X hX := by
  obtain ⟨S, hSh, hSS, hS⟩ :=
    exists_selfAdjoint_involution_trace_eq_traceNormH (Φ X) (hΦ.isHermitian_map hX)
  have hc := isHermContraction_of_involution hSh hSS
  rw [← hS, ← dual_spec]
  exact trace_mul_re_le_traceNormH X hX
    (hc.map (dual_positive_of_positive Φ hΦ) (one_sub_dualMap_one_posSemidef hΦ hT))

/-- Trace distance contracts under positive trace-nonincreasing maps. -/
theorem traceDist_map_le_of_isSTP {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΦ : IsPositiveMap Φ) (hT : IsSTP Φ) {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) :
    traceDist (Φ ρ) (Φ σ) (hΦ ρ hρ) (hΦ σ hσ)
        ((hΦ ρ hρ).isHermitian.sub (hΦ σ hσ).isHermitian) ≤
      traceDist ρ σ hρ hσ (hρ.isHermitian.sub hσ.isHermitian) := by
  have key := traceNormH_map_le_of_isSTP hΦ hT (ρ - σ) (hρ.isHermitian.sub hσ.isHermitian)
  have heq : traceNormH (Φ ρ - Φ σ) ((hΦ ρ hρ).isHermitian.sub (hΦ σ hσ).isHermitian) =
      traceNormH (Φ (ρ - σ)) (hΦ.isHermitian_map (hρ.isHermitian.sub hσ.isHermitian)) := by
    congr 1; rw [map_sub]
  unfold traceDist
  rw [heq]
  linarith

/-- A CPTP map does not increase the trace norm of a Hermitian matrix. -/
theorem traceNormH_map_le (Φ : CPTPMap n) (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    traceNormH (Φ.toLinearMap X) (Φ.positive.isHermitian_map hX) ≤ traceNormH X hX :=
  traceNormH_map_le_of_isSTP Φ.positive Φ.tp.isSTP X hX

/-- Trace distance contracts under CPTP maps. -/
theorem traceDist_map_le (Φ : CPTPMap n) {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) :
    traceDist (Φ.toLinearMap ρ) (Φ.toLinearMap σ) (Φ.positive ρ hρ) (Φ.positive σ hσ)
        ((Φ.positive ρ hρ).isHermitian.sub (Φ.positive σ hσ).isHermitian) ≤
      traceDist ρ σ hρ hσ (hρ.isHermitian.sub hσ.isHermitian) :=
  traceDist_map_le_of_isSTP Φ.positive Φ.tp.isSTP hρ hσ

end Quantum
