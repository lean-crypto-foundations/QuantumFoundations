/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.Instrument
public import QuantumFoundations.CPMap
public import QuantumFoundations.DualMap
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Petz Recovery Map: Quantum Bayesian Inversion

The Petz recovery map is the quantum analogue of classical Bayesian inversion.
Given a quantum channel (CPTP map) `Φ` and a full-rank reference state `σ`,
the Petz recovery map `R_{σ,Φ}` satisfies the quantum analogue of Bayes' theorem.

## Mathematical definition

```
R_{σ,Φ}(X) = σ^{1/2} Φ†[ Φ(σ)^{-1/2} X Φ(σ)^{-1/2} ] σ^{1/2}
```

where `Φ†` is the trace dual `dualMap Φ`, the linear map with `tr(Φ†(A) B) = tr(A Φ(B))`.
For a positive `Φ`, the only case used here, it is the Hilbert–Schmidt adjoint
(`dual_spec_conjTranspose`, `IsPositiveMap.map_conjTranspose`).

## Key properties

* CP (completely positive) when σ has full support
* CPTP (trace-preserving) when σ full rank and Φ is CPTP
* Exact recovery at reference: `R_{σ,Φ}(Φ(σ)) = σ`
* Compositionality: `R_{σ,Φ₂∘Φ₁} = R_{σ,Φ₁} ∘ R_{Φ₁(σ),Φ₂}`
* Unique retrodiction functor (Parzygnat-Buscemi 2023)

## Novel contribution

The observation that the Petz recovery map is the canonical conjoint in the
framed bicategory of QComp, combining:
* Parzygnat-Buscemi (2023): Petz = unique retrodiction functor
* Smithe (2020): Bayesian updates = optics/lenses
* Shulman (2008): lenses = conjoints in double categories

## Infrastructure status

* Matrix square root (`psdSqrt`): Fully proved via the unital CFC
  `Matrix.IsHermitian.cfc Real.sqrt`.
* Inverse square root (`psdInvSqrt`): Defined via `cfc (fun x => (√x)⁻¹)`.
  Proved for invertible (positive definite) matrices; for singular M
  the off-spectrum convention `0⁻¹ = 0` gives the Moore-Penrose inverse.
* `psdSqrt_mul_psdSqrt`: Fully proved.
* `psdInvSqrt_mul_psdSqrt`: Proved for invertible M.
* `psdInvSqrt_mul_psdSqrt_eq_cfc`: for every PSD M, `psdInvSqrt M * psdSqrt M` is the
  support projection of M.

## Properties of the Petz map

* `petzRecovery_cp`: positivity, given positivity of `Φ†` and Hermiticity of
  `Φ(σ)^{-1/2}` as hypotheses
* `petzRecovery_stp`: sub-trace-preservation, for every positive `Φ`
* `petzRecovery_exact`: exact recovery `R(Φ(σ)) = σ`, for invertible `Φ(σ)` and unital `Φ†`
* `petzRecovery_comp`: compositionality, for positive `Φ₁`, `Φ₂`

## References

* Parzygnat-Buscemi, "Axioms for retrodiction" (Quantum 7, 2023)
* Parzygnat, "Inverses, disintegrations, and Bayesian inversion in quantum Markov categories"
* Smithe, "Bayesian Updates Compose Optically" (arXiv:2006.01631)
* Fawzi-Renner, "Quantum conditional mutual information" (arXiv:1410.0664)
-/

@[expose] public section

open scoped Matrix ComplexOrder ENNReal
open Matrix

noncomputable section

namespace Quantum

variable {d : ℕ}

-- The Loewner order instances are not found automatically; register them locally.
attribute [local instance] instPartialOrder Matrix.instStarOrderedRing
  Matrix.instNonnegSpectrumClass

/-! ## Matrix Square Root via CFC

The continuous functional calculus (CFC) in Mathlib provides `CFC.sqrt`
for elements in a C*-algebra with nonneg spectrum. For PSD matrices
`M >= 0`, `CFC.sqrt M` satisfies `CFC.sqrt M * CFC.sqrt M = M` and
is itself PSD. -/

/-- Square root of a PSD matrix, via the unital continuous functional
    calculus on Hermitian matrices.

    For a PSD matrix `M`, `M.PosSemidef.isHermitian` gives the Hermitian
    structure, and `Matrix.IsHermitian.cfc Real.sqrt` realizes the
    spectral square root concretely via eigendecomposition. -/
noncomputable def psdSqrt (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    Matrix (Fin d) (Fin d) ℂ :=
  hM.isHermitian.cfc Real.sqrt

/-- Inverse square root on the support of a PSD matrix, via the unital CFC.

    For PSD `M`, we apply `(√x)⁻¹` on the spectrum (zero at the origin
    by the convention `0⁻¹ = 0`). The eigenvector unitary structure of
    `hM.isHermitian.cfc` makes this the Moore-Penrose inverse of √M. -/
noncomputable def psdInvSqrt (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    Matrix (Fin d) (Fin d) ℂ :=
  hM.isHermitian.cfc (fun x => (Real.sqrt x)⁻¹)

/-- Helper: spectrum of a PSD matrix (over ℝ) is range of its eigenvalues. -/
private lemma spectrum_real_nonneg_of_posSemidef
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    ∀ x ∈ spectrum ℝ M, (0 : ℝ) ≤ x := by
  intro x hx
  rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hM.eigenvalues_nonneg i

open scoped MatrixOrder in
/-- `psdSqrt M * psdSqrt M = M` for PSD matrices.

    Goes through the unital CFC: `√x · √x = x` on the spectrum of `M`
    (which is nonneg for PSD), so `cfc Real.sqrt M * cfc Real.sqrt M
    = cfc (id) M = M` by `cfc_mul`, `cfc_congr`, `cfc_id`. -/
theorem psdSqrt_mul_psdSqrt (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    psdSqrt M hM * psdSqrt M hM = M := by
  simp only [psdSqrt, ← hM.isHermitian.cfc_eq]
  rw [← cfc_mul Real.sqrt Real.sqrt M,
      cfc_congr (f := fun x => Real.sqrt x * Real.sqrt x) (g := id)
        (fun x hx => Real.mul_self_sqrt (spectrum_real_nonneg_of_posSemidef M hM x hx))]
  exact cfc_id ℝ M hM.isHermitian.isSelfAdjoint

open scoped MatrixOrder in
/-- `psdSqrt M` is PSD.

    Goes through the unital CFC: `cfc Real.sqrt M` is `0 ≤ -` because
    `Real.sqrt` is nonneg on the spectrum, so `cfc_nonneg` applies;
    then `nonneg_iff_posSemidef.mp` converts. -/
theorem psdSqrt_posSemidef (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    (psdSqrt M hM).PosSemidef := by
  rw [psdSqrt, ← hM.isHermitian.cfc_eq, ← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)

open scoped MatrixOrder in
/-- `psdInvSqrt M * psdSqrt M = 1` when M is invertible (positive definite).
    For singular M, psdInvSqrt is zero (Ring.inverse of non-unit).

    On the spectrum (positive for PosDef M), `(√x)⁻¹ · √x = 1`, so
    `cfc (fun x => (√x)⁻¹ · √x) M = cfc (fun _ => 1) M = 1`. -/
theorem psdInvSqrt_mul_psdSqrt (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef)
    (hU : IsUnit M) :
    psdInvSqrt M hM * psdSqrt M hM = 1 := by
  -- PosDef: PosSemidef + invertible. Spectrum is in (0,∞).
  have hPD : M.PosDef := hM.posDef_iff_isUnit.mpr hU
  have h_spec_pos : ∀ x ∈ spectrum ℝ M, (0 : ℝ) < x := by
    intro x hx
    rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hPD.eigenvalues_pos i
  have h_cont_invsqrt : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ M) :=
    (Real.continuous_sqrt.continuousOn).inv₀ (fun x hx =>
      Real.sqrt_pos.mpr (h_spec_pos x hx) |>.ne')
  have h_cont_sqrt : ContinuousOn (fun x : ℝ => Real.sqrt x) (spectrum ℝ M) :=
    Real.continuous_sqrt.continuousOn
  simp only [psdInvSqrt, psdSqrt, ← hM.isHermitian.cfc_eq]
  rw [← cfc_mul _ _ M h_cont_invsqrt h_cont_sqrt,
      cfc_congr (f := fun x => (Real.sqrt x)⁻¹ * Real.sqrt x) (g := fun _ => (1 : ℝ))
        (fun x hx => by
          have hpos := h_spec_pos x hx
          have h_ne : Real.sqrt x ≠ 0 := Real.sqrt_pos.mpr hpos |>.ne'
          field_simp),
      cfc_const_one ℝ M]

open scoped MatrixOrder in
/-- `psdSqrt M * psdInvSqrt M = 1` when M is invertible (positive definite).
    Symmetric to `psdInvSqrt_mul_psdSqrt`. -/
theorem psdSqrt_mul_psdInvSqrt (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef)
    (hU : IsUnit M) :
    psdSqrt M hM * psdInvSqrt M hM = 1 := by
  have hPD : M.PosDef := hM.posDef_iff_isUnit.mpr hU
  have h_spec_pos : ∀ x ∈ spectrum ℝ M, (0 : ℝ) < x := by
    intro x hx
    rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hPD.eigenvalues_pos i
  have h_cont_invsqrt : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ M) :=
    (Real.continuous_sqrt.continuousOn).inv₀ (fun x hx =>
      Real.sqrt_pos.mpr (h_spec_pos x hx) |>.ne')
  have h_cont_sqrt : ContinuousOn (fun x : ℝ => Real.sqrt x) (spectrum ℝ M) :=
    Real.continuous_sqrt.continuousOn
  simp only [psdInvSqrt, psdSqrt, ← hM.isHermitian.cfc_eq]
  rw [← cfc_mul _ _ M h_cont_sqrt h_cont_invsqrt,
      cfc_congr (f := fun x => Real.sqrt x * (Real.sqrt x)⁻¹) (g := fun _ => (1 : ℝ))
        (fun x hx => by
          have hpos := h_spec_pos x hx
          have h_ne : Real.sqrt x ≠ 0 := Real.sqrt_pos.mpr hpos |>.ne'
          field_simp),
      cfc_const_one ℝ M]

/-! ## Support projections

For PSD `M`, `psdInvSqrt M * psdSqrt M` is the functional calculus of the indicator of the
nonzero reals, the orthogonal projection onto the support of `M`. -/

/-- Every real function is continuous on the real spectrum of a matrix, which is finite. -/
private lemma continuousOn_spectrum_matrix (M : Matrix (Fin d) (Fin d) ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) :=
  Matrix.finite_real_spectrum.continuousOn f

open scoped MatrixOrder in
/-- `psdInvSqrt M * psdSqrt M` is the support projection of a PSD matrix `M`. -/
theorem psdInvSqrt_mul_psdSqrt_eq_cfc (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    psdInvSqrt M hM * psdSqrt M hM = cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) M := by
  simp only [psdInvSqrt, psdSqrt, ← hM.isHermitian.cfc_eq]
  rw [← cfc_mul _ _ M (continuousOn_spectrum_matrix M _) (continuousOn_spectrum_matrix M _)]
  refine cfc_congr fun x hx => ?_
  have hx0 := spectrum_real_nonneg_of_posSemidef M hM x hx
  by_cases h : x = 0
  · simp [h]
  · have hs : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx0 (Ne.symm h))
    simp [h, hs]

open scoped MatrixOrder in
/-- `psdSqrt M * psdInvSqrt M` is the support projection of a PSD matrix `M`. -/
theorem psdSqrt_mul_psdInvSqrt_eq_cfc (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    psdSqrt M hM * psdInvSqrt M hM = cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) M := by
  simp only [psdInvSqrt, psdSqrt, ← hM.isHermitian.cfc_eq]
  rw [← cfc_mul _ _ M (continuousOn_spectrum_matrix M _) (continuousOn_spectrum_matrix M _)]
  refine cfc_congr fun x hx => ?_
  have hx0 := spectrum_real_nonneg_of_posSemidef M hM x hx
  by_cases h : x = 0
  · simp [h]
  · have hs : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx0 (Ne.symm h))
    simp [h, hs]

open scoped MatrixOrder in
/-- The functional calculus of a `{0,1}`-valued function is idempotent. -/
private lemma cfc_mul_self_of_idem (M : Matrix (Fin d) (Fin d) ℂ) (f : ℝ → ℝ)
    (hf : ∀ x, f x * f x = f x) : cfc f M * cfc f M = cfc f M := by
  rw [← cfc_mul _ _ M (continuousOn_spectrum_matrix M _) (continuousOn_spectrum_matrix M _)]
  exact cfc_congr fun x _ => hf x

open scoped MatrixOrder in
/-- The functional calculus of a real function is Hermitian. -/
private lemma cfc_conjTranspose (M : Matrix (Fin d) (Fin d) ℂ) (f : ℝ → ℝ) :
    (cfc f M)ᴴ = cfc f M := by
  have h : IsSelfAdjoint (cfc f M) := cfc_predicate f M
  rwa [IsSelfAdjoint, Matrix.star_eq_conjTranspose] at h

open scoped MatrixOrder in
/-- The functional calculus of a nonnegative real function is PSD. -/
private lemma cfc_posSemidef_of_nonneg (M : Matrix (Fin d) (Fin d) ℂ) (f : ℝ → ℝ)
    (hf : ∀ x, 0 ≤ f x) : (cfc f M).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg fun x _ => hf x)

open scoped MatrixOrder in
/-- The support projection of a Hermitian matrix and its complement sum to `1`. -/
private lemma cfc_supp_add_ker (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.IsHermitian) :
    cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) M
      + cfc (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) M = 1 := by
  rw [← cfc_add (fun x : ℝ => if x = 0 then (0 : ℝ) else 1)
      (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) (a := M)
      (continuousOn_spectrum_matrix M _) (continuousOn_spectrum_matrix M _),
    cfc_congr (g := fun _ => (1 : ℝ)) (fun x _ => by by_cases h : x = 0 <;> simp [h]),
    cfc_const_one ℝ M hM.isSelfAdjoint]

/-- For PSD `W` and a Hermitian idempotent `Q`, `tr(Q W) = 0` forces `Q * W = 0`. -/
private lemma mul_eq_zero_of_trace_mul_eq_zero {Q W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W.PosSemidef) (hQh : Qᴴ = Q) (hQQ : Q * Q = Q) (htr : (Q * W).trace = 0) :
    Q * W = 0 := by
  have hSh : (psdSqrt W hW)ᴴ = psdSqrt W hW := (psdSqrt_posSemidef W hW).isHermitian
  have hA : Q * psdSqrt W hW = 0 := by
    rw [← trace_mul_conjTranspose_self_eq_zero_iff, conjTranspose_mul, hQh, hSh]
    have h1 : Q * psdSqrt W hW * (psdSqrt W hW * Q) = Q * (W * Q) := by
      conv_rhs => rw [← psdSqrt_mul_psdSqrt W hW]
      simp only [Matrix.mul_assoc]
    rw [h1, trace_mul_comm, Matrix.mul_assoc, hQQ, trace_mul_comm, htr]
  rw [← psdSqrt_mul_psdSqrt W hW, ← Matrix.mul_assoc, hA, Matrix.zero_mul]

open scoped MatrixOrder in
/-- A linear map on matrices that vanishes on every PSD matrix vanishes identically:
    every matrix is a complex combination of four PSD matrices. -/
private lemma linearMap_eq_zero_of_posSemidef
    (f : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hf : ∀ B, B.PosSemidef → f B = 0) (B : Matrix (Fin d) (Fin d) ℂ) : f B = 0 := by
  have herm : ∀ H : Matrix (Fin d) (Fin d) ℂ, H.IsHermitian → f H = 0 := by
    intro H hH
    have hdec : H = cfc (fun x : ℝ => max x 0) H - cfc (fun x : ℝ => max (-x) 0) H := by
      rw [← cfc_sub _ _ H (continuousOn_spectrum_matrix H _) (continuousOn_spectrum_matrix H _)]
      conv_lhs => rw [← cfc_id' ℝ H hH.isSelfAdjoint]
      exact cfc_congr fun x _ => by rcases le_total 0 x with h | h <;> simp [h]
    rw [hdec, map_sub, hf _ (cfc_posSemidef_of_nonneg H _ fun x => le_max_right _ _),
      hf _ (cfc_posSemidef_of_nonneg H _ fun x => le_max_right _ _), sub_zero]
  have h1 : ((1 / 2 : ℂ) • (B + Bᴴ)).IsHermitian := by
    ext i j
    simp [add_comm, mul_add]
  have h2 : ((-Complex.I / 2) • (B - Bᴴ)).IsHermitian := by
    ext i j
    simp [Complex.conj_I]
    ring
  have hB : B = (1 / 2 : ℂ) • (B + Bᴴ) + Complex.I • ((-Complex.I / 2) • (B - Bᴴ)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination (1 / 2 : ℂ) * (B i j - Bᴴ i j) * Complex.I_sq
  rw [hB, map_add, herm _ h1, map_smul, herm _ h2, smul_zero, add_zero]

/-! ## Petz Recovery Map -/

/-- The Petz recovery map for a quantum channel Φ at reference state σ.

    `R_{σ,Φ}(X) = σ^{1/2} Φ†[ Φ(σ)^{-1/2} X Φ(σ)^{-1/2} ] σ^{1/2}`

    This is the unique retrodiction functor (Parzygnat-Buscemi 2023) and
    the canonical quantum conjoint in the framed bicategory of QComp. -/
noncomputable def petzRecovery
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef)
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hΦ_cp : ∀ ρ, ρ.PosSemidef → (Φ ρ).PosSemidef) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  let σ_half := psdSqrt σ hσ
  let Φσ := Φ σ
  let hΦσ : Φσ.PosSemidef := hΦ_cp σ hσ
  let Φσ_inv_half := psdInvSqrt Φσ hΦσ
  let Φ_dag := dualMap Φ
  -- R(X) = σ^{1/2} Φ†[ Φ(σ)^{-1/2} X Φ(σ)^{-1/2} ] σ^{1/2}
  { toFun := fun X => σ_half * (Φ_dag (Φσ_inv_half * X * Φσ_inv_half)) * σ_half
    map_add' := by
      intro X Y
      simp only [mul_add, add_mul, map_add]
    map_smul' := by
      intro c X
      simp only [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply] }

/-! ## Properties of the Petz Map -/

/-- The Petz recovery map is completely positive.

    The proof uses: (1) psdInvSqrt is Hermitian, so sandwiching preserves PSD,
    (2) the dual map Φ† preserves PSD (added as hypothesis), and
    (3) psdSqrt is Hermitian (PSD → Hermitian), so outer sandwich preserves PSD. -/
theorem petzRecovery_cp
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef)
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hΦ_cp : ∀ ρ, ρ.PosSemidef → (Φ ρ).PosSemidef)
    (hΦ_dual_cp : ∀ ρ, ρ.PosSemidef → (dualMap Φ ρ).PosSemidef)
    (h_invSqrt_sa : (psdInvSqrt (Φ σ) (hΦ_cp σ hσ))ᴴ = psdInvSqrt (Φ σ) (hΦ_cp σ hσ)) :
    ∀ ρ, ρ.PosSemidef → (petzRecovery σ hσ Φ hΦ_cp ρ).PosSemidef := by
  intro ρ hρ
  simp only [petzRecovery, LinearMap.coe_mk, AddHom.coe_mk]
  -- Step 1: inner sandwich Φ(σ)^{-1/2} * ρ * Φ(σ)^{-1/2} is PSD
  have h1 : (psdInvSqrt (Φ σ) (hΦ_cp σ hσ) * ρ *
    psdInvSqrt (Φ σ) (hΦ_cp σ hσ)).PosSemidef := by
    rw [show psdInvSqrt (Φ σ) (hΦ_cp σ hσ) * ρ *
      psdInvSqrt (Φ σ) (hΦ_cp σ hσ) =
      psdInvSqrt (Φ σ) (hΦ_cp σ hσ) * ρ *
      (psdInvSqrt (Φ σ) (hΦ_cp σ hσ))ᴴ from by rw [h_invSqrt_sa]]
    exact hρ.mul_mul_conjTranspose_same _
  -- Step 2: Φ†(PSD) is PSD
  have h2 := hΦ_dual_cp _ h1
  -- Step 3: outer sandwich σ^{1/2} * PSD * σ^{1/2} is PSD
  have h_sqrt_sa : (psdSqrt σ hσ)ᴴ = psdSqrt σ hσ :=
    (psdSqrt_posSemidef σ hσ).isHermitian
  rw [show psdSqrt σ hσ * dualMap Φ _ * psdSqrt σ hσ =
    psdSqrt σ hσ * dualMap Φ _ * (psdSqrt σ hσ)ᴴ from by rw [h_sqrt_sa]]
  exact h2.mul_mul_conjTranspose_same _

/-- The Petz recovery map is sub-trace-preserving on PSD inputs, for every positive `Φ`.

    By `dual_spec`, `tr R(ρ) = tr(ρ · Π)` with `Π = Φ(σ)^{-1/2} Φ(σ) Φ(σ)^{-1/2}` the support
    projection of `Φ(σ)`; `1 - Π` is PSD, so `Re tr(ρ (1 - Π)) ≥ 0`.

    **Reference**: D. Petz, "Sufficiency of channels over von Neumann algebras" (1988). -/
theorem petzRecovery_stp
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef)
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hΦ_cp : ∀ ρ, ρ.PosSemidef → (Φ ρ).PosSemidef) :
    ∀ ρ, ρ.PosSemidef →
      (petzRecovery σ hσ Φ hΦ_cp ρ).trace.re ≤ ρ.trace.re := by
  intro ρ hρ
  have hM : (Φ σ).PosSemidef := hΦ_cp σ hσ
  have hJMJ : psdInvSqrt (Φ σ) hM * Φ σ * psdInvSqrt (Φ σ) hM
      = cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (Φ σ) := by
    calc psdInvSqrt (Φ σ) hM * Φ σ * psdInvSqrt (Φ σ) hM
        = psdInvSqrt (Φ σ) hM * (psdSqrt (Φ σ) hM * psdSqrt (Φ σ) hM) *
            psdInvSqrt (Φ σ) hM := by rw [psdSqrt_mul_psdSqrt]
      _ = (psdInvSqrt (Φ σ) hM * psdSqrt (Φ σ) hM) *
            (psdSqrt (Φ σ) hM * psdInvSqrt (Φ σ) hM) := by simp only [Matrix.mul_assoc]
      _ = cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (Φ σ) *
            cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (Φ σ) := by
          rw [psdInvSqrt_mul_psdSqrt_eq_cfc, psdSqrt_mul_psdInvSqrt_eq_cfc]
      _ = cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (Φ σ) :=
          cfc_mul_self_of_idem _ _ (fun x => by by_cases h : x = 0 <;> simp [h])
  have htr : (petzRecovery σ hσ Φ hΦ_cp ρ).trace
      = (ρ * cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (Φ σ)).trace := by
    simp only [petzRecovery, LinearMap.coe_mk, AddHom.coe_mk]
    rw [trace_mul_comm, ← Matrix.mul_assoc, psdSqrt_mul_psdSqrt, trace_mul_comm, dual_spec,
      ← hJMJ]
    simp only [Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hP := eq_sub_of_add_eq (cfc_supp_add_ker (Φ σ) hM.isHermitian)
  have hG := cfc_posSemidef_of_nonneg (Φ σ) (fun x : ℝ => if x = 0 then (1 : ℝ) else 0)
    (fun x => by by_cases h : x = 0 <;> simp [h])
  have hnn := (Complex.le_def.mp (trace_psd_mul_psd_nonneg ρ _ hρ hG)).1
  rw [htr, hP, Matrix.mul_sub, Matrix.mul_one, trace_sub, Complex.sub_re]
  simp only [Complex.zero_re] at hnn
  linarith

/-- Exact recovery at the reference state: R_{σ,Φ}(Φ(σ)) = σ.

    This is the quantum analogue of `bayesInv_recovery`. Requires that
    Φ(σ) is invertible (positive definite) and Φ† is unital (holds for TP maps). -/
theorem petzRecovery_exact
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef)
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hΦ_cp : ∀ ρ, ρ.PosSemidef → (Φ ρ).PosSemidef)
    (hU : IsUnit (Φ σ))
    (h_unital : dualMap Φ 1 = 1) :
    petzRecovery σ hσ Φ hΦ_cp (Φ σ) = σ := by
  have hΦσ : (Φ σ).PosSemidef := hΦ_cp σ hσ
  -- Step 1: Φ(σ)^{-1/2} · Φ(σ) · Φ(σ)^{-1/2} = 1
  have h_inner : psdInvSqrt (Φ σ) hΦσ * Φ σ * psdInvSqrt (Φ σ) hΦσ = 1 := by
    calc psdInvSqrt (Φ σ) hΦσ * Φ σ * psdInvSqrt (Φ σ) hΦσ
        = psdInvSqrt (Φ σ) hΦσ * (psdSqrt (Φ σ) hΦσ * psdSqrt (Φ σ) hΦσ) *
          psdInvSqrt (Φ σ) hΦσ := by congr 1; congr 1; exact (psdSqrt_mul_psdSqrt _ _).symm
      _ = (psdInvSqrt (Φ σ) hΦσ * psdSqrt (Φ σ) hΦσ) *
          (psdSqrt (Φ σ) hΦσ * psdInvSqrt (Φ σ) hΦσ) := by simp only [mul_assoc]
      _ = 1 * 1 := by rw [psdInvSqrt_mul_psdSqrt _ _ hU, psdSqrt_mul_psdInvSqrt _ _ hU]
      _ = 1 := one_mul 1
  -- Step 2: Unfold and simplify
  simp only [petzRecovery, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h_inner, h_unital, mul_one, psdSqrt_mul_psdSqrt]

/-- For a positive map `Φ` and PSD `σ`, compressing the argument of `Φ†` to the support
    projection `P` of `Φ(σ)` does not change `σ^{1/2} Φ†(·) σ^{1/2}`:
    `σ^{1/2} Φ†(P Y P) σ^{1/2} = σ^{1/2} Φ†(Y) σ^{1/2}`.

    With `Q = 1 - P`, `σ^{1/2} Φ†(Q) σ^{1/2}` is PSD with trace `tr(Q Φ(σ)) = 0`, hence zero;
    so `tr(Q Φ(σ^{1/2} B σ^{1/2})) = 0` for every `B`, which for PSD `B` forces
    `Q Φ(σ^{1/2} B σ^{1/2}) = 0`, and PSD matrices span all matrices. -/
theorem dualMap_sandwich_supportProj
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef)
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hΦ : ∀ ρ, ρ.PosSemidef → (Φ ρ).PosSemidef) (Y : Matrix (Fin d) (Fin d) ℂ) :
    psdSqrt σ hσ * dualMap Φ (cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (Φ σ) * Y *
        cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (Φ σ)) * psdSqrt σ hσ
      = psdSqrt σ hσ * dualMap Φ Y * psdSqrt σ hσ := by
  have hT : (Φ σ).PosSemidef := hΦ σ hσ
  have hSh : (psdSqrt σ hσ)ᴴ = psdSqrt σ hσ := (psdSqrt_posSemidef σ hσ).isHermitian
  have hSS : psdSqrt σ hσ * psdSqrt σ hσ = σ := psdSqrt_mul_psdSqrt σ hσ
  have hPQ := eq_sub_of_add_eq (cfc_supp_add_ker (Φ σ) hT.isHermitian)
  have hQh := cfc_conjTranspose (Φ σ) (fun x : ℝ => if x = 0 then (1 : ℝ) else 0)
  have hQQ := cfc_mul_self_of_idem (Φ σ) (fun x : ℝ => if x = 0 then (1 : ℝ) else 0)
    (fun x => by by_cases h : x = 0 <;> simp [h])
  have hQpsd := cfc_posSemidef_of_nonneg (Φ σ) (fun x : ℝ => if x = 0 then (1 : ℝ) else 0)
    (fun x => by by_cases h : x = 0 <;> simp [h])
  have hQT : cfc (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) (Φ σ) * Φ σ = 0 := by
    have h := (cfc_mul (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) (fun x : ℝ => x) (Φ σ)
      (continuousOn_spectrum_matrix _ _) (continuousOn_spectrum_matrix _ _)).symm
    rw [cfc_id' ℝ (Φ σ) hT.isHermitian.isSelfAdjoint,
      cfc_congr (f := fun x : ℝ => (if x = 0 then (1 : ℝ) else 0) * x) (g := 0)
        (fun x _ => by by_cases hx : x = 0 <;> simp [hx]), cfc_zero] at h
    exact h
  set S := psdSqrt σ hσ with hS
  set P := cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (Φ σ) with hP
  set Q := cfc (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) (Φ σ) with hQ
  have hD : S * dualMap Φ Q * S = 0 := by
    have hpsd : (S * dualMap Φ Q * S).PosSemidef := by
      have := (dual_positive_of_positive Φ hΦ Q hQpsd).mul_mul_conjTranspose_same S
      rwa [hSh] at this
    refine hpsd.trace_eq_zero_iff.mp ?_
    rw [trace_mul_comm, ← Matrix.mul_assoc, hSS, trace_mul_comm, dual_spec, hQT, trace_zero]
  have hcyc : ∀ Z B : Matrix (Fin d) (Fin d) ℂ,
      (S * Z * S * B).trace = (Z * (S * B * S)).trace := by
    intro Z B
    rw [show S * Z * S * B = S * (Z * S * B) by simp only [Matrix.mul_assoc], trace_mul_comm S]
    simp only [Matrix.mul_assoc]
  have hW : ∀ B, B.PosSemidef → Q * Φ (S * B * S) = 0 ∧ Φ (S * B * S) * Q = 0 := by
    intro B hB
    have hWpsd : (Φ (S * B * S)).PosSemidef := hΦ _ (by
      have := hB.mul_mul_conjTranspose_same S
      rwa [hSh] at this)
    have h1 : Q * Φ (S * B * S) = 0 := by
      refine mul_eq_zero_of_trace_mul_eq_zero hWpsd hQh hQQ ?_
      rw [← dual_spec, ← hcyc, hD, Matrix.zero_mul, trace_zero]
    refine ⟨h1, ?_⟩
    have := congrArg conjTranspose h1
    rwa [conjTranspose_mul, hQh, hWpsd.isHermitian.eq, conjTranspose_zero] at this
  have hall : ∀ B, Q * Φ (S * B * S) = 0 ∧ Φ (S * B * S) * Q = 0 := by
    intro B
    let L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
      Φ ∘ₗ (LinearMap.mulRight ℂ S ∘ₗ LinearMap.mulLeft ℂ S)
    exact ⟨linearMap_eq_zero_of_posSemidef (LinearMap.mulLeft ℂ Q ∘ₗ L)
        (fun B hB => (hW B hB).1) B,
      linearMap_eq_zero_of_posSemidef (LinearMap.mulRight ℂ Q ∘ₗ L)
        (fun B hB => (hW B hB).2) B⟩
  ext i j
  rw [← trace_mul_matUnit (S * dualMap Φ (P * Y * P) * S) i j,
    ← trace_mul_matUnit (S * dualMap Φ Y * S) i j, hcyc, hcyc,
    dual_spec, dual_spec]
  obtain ⟨h1, h2⟩ := hall (matUnit j i)
  have hPW : P * Φ (S * matUnit j i * S) * P = Φ (S * matUnit j i * S) := by
    rw [hPQ, Matrix.sub_mul, Matrix.one_mul, h1, sub_zero, Matrix.mul_sub, Matrix.mul_one, h2,
      sub_zero]
  generalize Φ (S * matUnit j i * S) = W at hPW ⊢
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm P, Matrix.mul_assoc, hPW]

/-- Compositionality of the Petz recovery map:
    `R_{σ,Φ₂∘Φ₁} = R_{σ,Φ₁} ∘ R_{Φ₁(σ),Φ₂}`, for positive `Φ₁`, `Φ₂` and PSD `σ`.

    `(Φ₂∘Φ₁)† = Φ₁† ∘ Φ₂†` reduces the claim to
    `σ^{1/2} Φ₁†(P Y P) σ^{1/2} = σ^{1/2} Φ₁†(Y) σ^{1/2}` with `P` the support projection of
    `Φ₁(σ)` (`dualMap_sandwich_supportProj`).

    **Reference**: D. Petz, "Sufficiency of channels over von Neumann algebras" (1988);
    M. Wilde, *Quantum Information Theory*, 2nd ed., §12.3. -/
theorem petzRecovery_comp
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef)
    (Φ₁ Φ₂ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hΦ₁ : ∀ ρ, ρ.PosSemidef → (Φ₁ ρ).PosSemidef)
    (hΦ₂ : ∀ ρ, ρ.PosSemidef → (Φ₂ ρ).PosSemidef) :
    ∀ X, petzRecovery σ hσ (Φ₂.comp Φ₁) (fun ρ hρ => hΦ₂ _ (hΦ₁ ρ hρ)) X =
      petzRecovery σ hσ Φ₁ hΦ₁ (petzRecovery (Φ₁ σ) (hΦ₁ σ hσ) Φ₂ hΦ₂ X) := by
  intro X
  simp only [petzRecovery, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dualMap_comp, LinearMap.comp_apply,
    show ∀ A B Y C D : Matrix (Fin d) (Fin d) ℂ, A * (B * Y * C) * D = (A * B) * Y * (C * D)
      from fun _ _ _ _ _ => by simp only [Matrix.mul_assoc],
    psdInvSqrt_mul_psdSqrt_eq_cfc, psdSqrt_mul_psdInvSqrt_eq_cfc,
    dualMap_sandwich_supportProj σ hσ Φ₁ hΦ₁]
  rfl

/-! ## Petz as QComp Instrument -/

/-- The Petz recovery as a QComp instrument (single outcome).
    This wraps the Petz recovery linear map into the QComp monad. -/
noncomputable def petzQComp
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef)
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hΦ_cp : ∀ ρ, ρ.PosSemidef → (Φ ρ).PosSemidef)
    (hΦ_dual_cp : ∀ ρ, ρ.PosSemidef → (dualMap Φ ρ).PosSemidef)
    (h_invSqrt_sa : (psdInvSqrt (Φ σ) (hΦ_cp σ hσ))ᴴ = psdInvSqrt (Φ σ) (hΦ_cp σ hσ)) :
    QComp d Unit where
  branch _ := petzRecovery σ hσ Φ hΦ_cp
  branch_psd _ := petzRecovery_cp σ hσ Φ hΦ_cp hΦ_dual_cp h_invSqrt_sa
  branch_summable ρ := by
    apply summable_of_ne_finset_zero (s := {()})
    intro b hb; simp at hb
  branch_stp ρ hρ := by
    rw [tsum_eq_single () (fun b hb => absurd rfl hb)]
    exact petzRecovery_stp σ hσ Φ hΦ_cp ρ hρ

/-! ## Petz Recovery = Quantum Conjoint

The Petz recovery map gives the canonical conjoint in the framed bicategory
of QComp. This combines three results:

1. **Parzygnat-Buscemi (2023)**: Petz = unique retrodiction functor
   (involutive monoidal functor States → States^{op})
2. **Smithe (2020)**: Bayesian updates = optics/lenses
   (forward Φ, backward R_{σ,Φ} form a Bayesian lens)
3. **Shulman (2008)**: lenses = conjoints in double categories
   (lawful lens ↔ companion-conjoint adjunction)

Formalizing the full connection requires:
- Defining "quantum tight maps" as CPTP channels
- Building the unit/counit 2-cells using `petzRecovery_exact`
- Proving the zig-zag identities

This is left as future work pending the matrix square root infrastructure. -/

-- Future: UCMonadFramed (QComp d) with Prior = DensityMatrix d

end Quantum
