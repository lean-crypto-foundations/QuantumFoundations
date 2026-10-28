/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.TraceNorm
public import QuantumFoundations.Instrument
public import QuantumFoundations.InstrumentCP
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order
public import QuantumFoundations.ForMathlib.MatrixPosSemidef

/-!
# Gentle Measurement Lemma

The gentle measurement lemma bounds the disturbance caused by a projective
measurement when the measurement outcome has high probability.

## Main Definitions

* `Projector` — self-adjoint idempotent matrix (orthogonal projector)
* `Projector.complement` — the complementary projector `I - P`

## Main Results

* `Projector.psd` — a projector is PSD
* `Projector.complement_psd` — the complement of a projector is PSD
* `Projector.trace_PρP_eq` — `tr(PρP) = tr(Pρ)` (cyclicity + idempotence)
* `Projector.complement_trace_le` — `tr((I-P)ρ) ≤ ε` when `tr(Pρ) ≥ 1 - ε`
* `Projector.gentle_decomposition` — `ρ - PρP = (I-P)ρ + Pρ(I-P)`
* `Projector.gentle_diff_hermitian` — `ρ - PρP` is Hermitian
* `Projector.PρP_psd` — `PρP` is PSD
* `trace_product_cs_bound` — Cauchy-Schwarz: `|tr(AρB†)|² ≤ tr(AρA†)·tr(BρB†)`
* `gentle_measurement` — `‖ρ - PρP‖₁ ≤ 2√ε`

## Mathematical Background

The gentle measurement lemma (Winter 1999, Ogawa-Nagaoka 2007) bounds the disturbance of a
likely measurement outcome. For a density matrix ρ and a projector P with `tr(Pρ) ≥ 1 - ε`,
the unnormalized post-measurement state `PρP` satisfies `‖ρ - PρP‖₁ ≤ 2√ε`, that is,
`½‖ρ - PρP‖₁ ≤ √ε`. This is the form proved here; the normalized post-measurement state
`PρP / tr(Pρ)` is not treated.

The proof decomposes `ρ - PρP = (I-P)ρ + Pρ(I-P)` and bounds each term
using Cauchy-Schwarz for the Hilbert-Schmidt inner product weighted by ρ.

## References

* Winter — Coding Theorem and Strong Converse for Quantum Channels, 1999
* Ogawa, Nagaoka — Making Good Codes for Classical-Quantum Channel Coding
  via Quantum Hypothesis Testing, 2007
* Wilde — Quantum Information Theory (Cambridge, 2017), Lemma 9.4.1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder
open Matrix

noncomputable section

namespace Quantum.GentleMeasurement

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Projector -/

namespace Projector

variable (P : Projector d) (ρ : Matrix d d ℂ)

/-- A projector is positive semidefinite.

    Proof: `P = P†P` (by self-adjointness and idempotence), which is PSD
    by `posSemidef_conjTranspose_mul_self`. -/
theorem psd : P.val.PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self P.val
  rw [P.self_adjoint, P.idempotent] at h
  exact h

/-- The complementary projector `I - P`. -/
def complement : Projector d where
  val := 1 - P.val
  self_adjoint := by
    rw [conjTranspose_sub, conjTranspose_one, P.self_adjoint]
  idempotent := by
    rw [sub_mul, one_mul, mul_sub, mul_one, P.idempotent, sub_self, sub_zero]

/-- The complement of a projector is PSD. -/
theorem complement_psd : (1 - P.val).PosSemidef :=
  P.complement.psd

/-- A projector is an effect (0 ≤ P ≤ I). -/
theorem isEffect : IsEffect P.val :=
  ⟨P.psd, P.complement_psd⟩

/-! ## Trace Bounds -/

/-- `tr(PρP) = tr(Pρ)` by cyclicity of trace and `P² = P`. -/
theorem trace_PρP_eq :
    (P.val * ρ * P.val).trace = (P.val * ρ).trace := by
  rw [trace_mul_cycle, P.idempotent]

/-- `tr(Pρ)` has zero imaginary part when ρ is Hermitian. -/
theorem trace_Pρ_real (hρ : ρ.IsHermitian) :
    (P.val * ρ).trace.im = 0 := by
  -- (Pρ)† = ρ†P† = ρP = Pρ... wait, Pρ is not necessarily self-adjoint.
  -- But tr(Pρ) = tr((Pρ)†)* and (Pρ)† = ρP, so tr(Pρ) = conj(tr(ρP)) = conj(tr(Pρ))
  have hconj : (P.val * ρ)ᴴ = ρ * P.val := by
    rw [conjTranspose_mul, hρ.eq, P.self_adjoint]
  have h1 : (P.val * ρ)ᴴ.trace = starRingEnd ℂ ((P.val * ρ).trace) :=
    Matrix.trace_conjTranspose _
  rw [hconj, trace_mul_comm] at h1
  exact Complex.conj_eq_iff_im.mp h1.symm

/-- Complement trace bound: `tr((I-P)ρ).re ≤ ε` when `tr(Pρ).re ≥ 1 - ε`.

    Proof: `tr((I-P)ρ) = tr(ρ) - tr(Pρ) = 1 - tr(Pρ)`. -/
theorem complement_trace_le (htr : ρ.trace = 1)
    (ε : ℝ) (h : (P.val * ρ).trace.re ≥ 1 - ε) :
    ((1 - P.val) * ρ).trace.re ≤ ε := by
  have hlin : ((1 - P.val) * ρ).trace = ρ.trace - (P.val * ρ).trace := by
    rw [sub_mul, one_mul, trace_sub]
  rw [hlin, htr, Complex.sub_re, Complex.one_re]
  linarith

/-- `tr((I-P)ρ(I-P)) = tr((I-P)ρ)` by cyclicity and `(I-P)² = I-P`. -/
theorem trace_QρQ_eq :
    ((1 - P.val) * ρ * (1 - P.val)).trace = ((1 - P.val) * ρ).trace := by
  rw [trace_mul_cycle]
  have : (1 - P.val) * (1 - P.val) = 1 - P.val := by
    rw [sub_mul, one_mul, mul_sub, mul_one, P.idempotent, sub_self, sub_zero]
  rw [this]

/-! ## PSD Preservation -/

/-- `PρP` is PSD when ρ is PSD. -/
theorem PρP_psd (hρ : ρ.PosSemidef) :
    (P.val * ρ * P.val).PosSemidef := by
  rw [show P.val * ρ * P.val = P.valᴴ * ρ * P.val from by rw [P.self_adjoint]]
  exact hρ.conjTranspose_mul_mul_same P.val

/-- `(I-P)ρ(I-P)` is PSD when ρ is PSD. -/
theorem QρQ_psd (hρ : ρ.PosSemidef) :
    ((1 - P.val) * ρ * (1 - P.val)).PosSemidef :=
  P.complement.PρP_psd ρ hρ

/-! ## Decomposition -/

/-- Key decomposition: `ρ - PρP = (I-P)ρ + Pρ(I-P)`.

    This splits the disturbance into two terms that can be bounded
    separately using Cauchy-Schwarz. -/
theorem gentle_decomposition :
    ρ - P.val * ρ * P.val =
    (1 - P.val) * ρ + P.val * ρ * (1 - P.val) := by
  have h1 : (1 - P.val) * ρ = ρ - P.val * ρ := by
    rw [sub_mul, one_mul]
  have h2 : P.val * ρ * (1 - P.val) = P.val * ρ - P.val * ρ * P.val := by
    rw [mul_sub, mul_one]
  rw [h1, h2, sub_add_sub_cancel]

/-- `ρ - PρP` is Hermitian when ρ is Hermitian. -/
theorem gentle_diff_hermitian (hρ : ρ.IsHermitian) :
    (ρ - P.val * ρ * P.val).IsHermitian := by
  apply IsHermitian.sub hρ
  change (P.val * ρ * P.val)ᴴ = P.val * ρ * P.val
  simp only [conjTranspose_mul, P.self_adjoint, hρ.eq, mul_assoc]

/-- The trace of `ρ - PρP` equals `tr(ρ) - tr(Pρ)`.

    When `tr(Pρ) ≈ 1`, this trace is small (≈ ε). -/
theorem gentle_diff_trace :
    (ρ - P.val * ρ * P.val).trace = ρ.trace - (P.val * ρ).trace := by
  rw [trace_sub, P.trace_PρP_eq]

/-! ## Orthogonality -/

/-- `PQ = 0` for complementary projectors. -/
theorem P_mul_Q : P.val * (1 - P.val) = 0 := by
  rw [mul_sub, mul_one, P.idempotent, sub_self]

/-- `QP = 0` for complementary projectors. -/
theorem Q_mul_P : (1 - P.val) * P.val = 0 := by
  rw [sub_mul, one_mul, P.idempotent, sub_self]

end Projector

/-! ## Hilbert-Schmidt Cauchy-Schwarz

The Cauchy-Schwarz inequality for the Hilbert-Schmidt inner product
weighted by a PSD matrix ρ:

`|tr(AρB†)|² ≤ tr(AρA†) · tr(BρB†)`

This is the key analytical tool for the gentle measurement bound.
-/

/-- Trace of a PSD-weighted outer product is non-negative:
    `0 ≤ tr(AρA†)` when ρ is PSD.

    Proof: `AρA† = A ρ^{1/2} (A ρ^{1/2})†`, which is PSD. -/
theorem trace_AρAstar_nonneg {ρ A : Matrix d d ℂ}
    (hρ : ρ.PosSemidef) :
    0 ≤ (A * ρ * Aᴴ).trace := by
  have h : (A * ρ * Aᴴ).PosSemidef := hρ.mul_mul_conjTranspose_same A
  rw [Complex.nonneg_iff]
  exact ⟨Quantum.trace_re_nonneg_of_psd h,
         (Quantum.trace_im_zero_of_psd h).symm⟩

private lemma normSq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := by
  simp [Complex.normSq_apply]

/-- **Cauchy-Schwarz for PSD-weighted trace products**.

    For PSD ρ and any matrices A, B:
    `|tr(AρB†)|² ≤ tr(AρA†)·re · tr(BρB†)·re`

    Proof: use Mathlib's `toMatrixInnerProductSpace` (ρ-weighted inner product
    where `⟪A, B⟫ = tr(BρA†)`) and apply `norm_inner_le_norm` (Cauchy-Schwarz),
    then square both sides. -/
theorem trace_product_cs_bound {ρ A B : Matrix d d ℂ}
    (hρ : ρ.PosSemidef) :
    Complex.normSq ((A * ρ * Bᴴ).trace) ≤
      (A * ρ * Aᴴ).trace.re * (B * ρ * Bᴴ).trace.re := by
  -- Step 1: normSq(tr(AρBᴴ)) = normSq(tr(BρAᴴ)) via conjugation
  have h_nseq : Complex.normSq ((A * ρ * Bᴴ).trace) =
      Complex.normSq ((B * ρ * Aᴴ).trace) := by
    have h : B * ρ * Aᴴ = (A * ρ * Bᴴ)ᴴ := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
          hρ.isHermitian.eq, mul_assoc]
    rw [h, trace_conjTranspose, normSq_star]
  rw [h_nseq]
  -- Step 2: Set up the ρ-weighted inner product space
  let _ : SeminormedAddCommGroup (Matrix d d ℂ) :=
    ρ.toMatrixSeminormedAddCommGroup hρ
  let _ : InnerProductSpace ℂ (Matrix d d ℂ) :=
    ρ.toMatrixInnerProductSpace hρ
  -- ⟪A, B⟫ = (B * ρ * Aᴴ).trace (definitional)
  -- Step 3: Rewrite as normSq of inner product
  change Complex.normSq (@inner ℂ _ _ A B) ≤
    (@inner ℂ _ _ A A).re * (@inner ℂ _ _ B B).re
  -- Step 4: normSq z = ‖z‖²
  rw [Complex.normSq_eq_norm_sq]
  -- Step 5: re⟪x,x⟫ = ‖x‖ * ‖x‖
  have hA : (@inner ℂ _ _ A A).re = ‖A‖ * ‖A‖ :=
    inner_self_eq_norm_mul_norm (𝕜 := ℂ) A
  have hB : (@inner ℂ _ _ B B).re = ‖B‖ * ‖B‖ :=
    inner_self_eq_norm_mul_norm (𝕜 := ℂ) B
  rw [hA, hB]
  -- Step 6: Cauchy-Schwarz + squaring
  have hCS := norm_inner_le_norm (𝕜 := ℂ) A B
  calc ‖@inner ℂ _ _ A B‖ ^ 2
      ≤ (‖A‖ * ‖B‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hCS 2
    _ = ‖A‖ * ‖A‖ * (‖B‖ * ‖B‖) := by ring

/-! ## Gentle Measurement Bound -/

/-- **Gentle Measurement Lemma** (for projective measurements).

    Let ρ be a density matrix (PSD, trace 1) and P a projector.
    If `tr(Pρ) ≥ 1 - ε`, then the trace norm of `ρ - PρP` is at most `2√ε`.

    Proof: choose a self-adjoint involution `S` with `‖ρ - PρP‖₁ = Re tr(S(ρ - PρP))`
    (`exists_selfAdjoint_involution_trace_eq_traceNormH`) and decompose
    `ρ - PρP = (I-P)ρ + Pρ(I-P)` (`gentle_decomposition`). By
    `trace_product_cs_bound`,
    `|tr(S(I-P)ρ)|² ≤ tr((I-P)ρ(I-P)) · tr(SρS) ≤ ε · 1` and
    `|tr(SPρ(I-P))|² ≤ tr(PρP) · tr(S(I-P)ρ(I-P)S) ≤ 1 · ε`;
    each term contributes at most `√ε`.

    **References**: Wilde, QIT Lemma 9.4.1; Winter 1999. -/
theorem gentle_measurement (P : Projector d)
    (ρ : Matrix d d ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (h_meas : (P.val * ρ).trace.re ≥ 1 - ε)
    (h_herm : (ρ - P.val * ρ * P.val).IsHermitian) :
    traceNormH (ρ - P.val * ρ * P.val) h_herm ≤ 2 * Real.sqrt ε := by
  obtain ⟨S, hSh, hSS, hS⟩ :=
    exists_selfAdjoint_involution_trace_eq_traceNormH _ h_herm
  have hQh : (1 - P.val)ᴴ = 1 - P.val := P.complement.self_adjoint
  have hQQ : ((1 - P.val) * ρ * (1 - P.val)).trace.re ≤ ε := by
    rw [P.trace_QρQ_eq]; exact P.complement_trace_le ρ htr ε h_meas
  have hQQ0 : 0 ≤ ((1 - P.val) * ρ * (1 - P.val)).trace.re :=
    trace_re_nonneg_of_psd (P.QρQ_psd ρ hρ)
  have hPP0 : 0 ≤ (P.val * ρ * P.val).trace.re :=
    trace_re_nonneg_of_psd (P.PρP_psd ρ hρ)
  have hPP1 : (P.val * ρ * P.val).trace.re ≤ 1 := by
    have hsplit : (P.val * ρ).trace = ρ.trace - ((1 - P.val) * ρ).trace := by
      rw [sub_mul, one_mul, trace_sub, sub_sub_cancel]
    rw [P.trace_PρP_eq, hsplit, htr, ← P.trace_QρQ_eq, Complex.sub_re,
      Complex.one_re]
    linarith
  have hSρS : (S * ρ * S).trace.re = 1 := by
    rw [trace_mul_cycle, hSS, one_mul, htr, Complex.one_re]
  -- First term: `Re tr(S (I-P) ρ) ≤ √ε`.
  have h1 : (S * ((1 - P.val) * ρ)).trace.re ≤ Real.sqrt ε := by
    apply Complex.re_le_sqrt_of_normSq_le
    have hcs := trace_product_cs_bound (A := 1 - P.val) (B := S) hρ
    rw [hSh, hQh, hSρS, mul_one] at hcs
    rw [trace_mul_comm]
    exact hcs.trans hQQ
  -- Second term: `Re tr(S P ρ (I-P)) ≤ √ε`.
  have h2 : (S * (P.val * ρ * (1 - P.val))).trace.re ≤ Real.sqrt ε := by
    apply Complex.re_le_sqrt_of_normSq_le
    have hcs := trace_product_cs_bound (A := P.val) (B := S * (1 - P.val)) hρ
    have hB : (S * (1 - P.val))ᴴ = (1 - P.val) * S := by
      rw [conjTranspose_mul, hSh, hQh]
    have hBB : (S * (1 - P.val) * ρ * ((1 - P.val) * S)).trace =
        ((1 - P.val) * ρ * (1 - P.val)).trace := by
      rw [show S * (1 - P.val) * ρ * ((1 - P.val) * S) =
          S * ((1 - P.val) * ρ * (1 - P.val)) * S by simp only [mul_assoc],
        trace_mul_cycle, hSS, one_mul]
    rw [hB, hBB, P.self_adjoint] at hcs
    rw [trace_mul_comm, show P.val * ρ * (1 - P.val) * S =
        P.val * ρ * ((1 - P.val) * S) by simp only [mul_assoc]]
    calc _ ≤ _ := hcs
      _ ≤ 1 * ε := mul_le_mul hPP1 hQQ hQQ0 zero_le_one
      _ = ε := one_mul ε
  rw [← hS, P.gentle_decomposition ρ, mul_add, trace_add, Complex.add_re]
  linarith

/-! ## Application: Trace Distance Form -/

/-- Gentle measurement in trace distance form:
    `traceDist ρ (PρP) ≤ √ε` (half the trace norm bound). -/
theorem gentle_measurement_traceDist (P : Projector d)
    (ρ : Matrix d d ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (h_meas : (P.val * ρ).trace.re ≥ 1 - ε)
    (h_herm : (ρ - P.val * ρ * P.val).IsHermitian) :
    (1/2 : ℝ) * traceNormH (ρ - P.val * ρ * P.val) h_herm ≤ Real.sqrt ε := by
  have h := gentle_measurement P ρ hρ htr ε hε h_meas h_herm
  linarith

/-! ## Complement Trace Bound -/

/-- The complement trace bound: `tr((I-P)ρ(I-P)) ≤ ε` for a density matrix `ρ` with
    `tr(Pρ) ≥ 1 - ε`. -/
theorem complement_sandwich_trace_le (P : Projector d)
    (ρ : Matrix d d ℂ) (htr : ρ.trace = 1)
    (ε : ℝ) (h_meas : (P.val * ρ).trace.re ≥ 1 - ε) :
    ((1 - P.val) * ρ * (1 - P.val)).trace.re ≤ ε := by
  rw [P.trace_QρQ_eq]
  exact P.complement_trace_le ρ htr ε h_meas

end Quantum.GentleMeasurement
