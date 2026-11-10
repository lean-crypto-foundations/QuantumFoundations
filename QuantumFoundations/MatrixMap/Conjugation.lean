/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.MatrixMap
public import QuantumFoundations.ForMathlib.Matrix.Contraction

/-!
# Conjugation, amplification and projections
-/

public section

open Matrix
open scoped Kronecker ComplexOrder

namespace Quantum.MatrixMap

section tensor

variable {A B R S : Type*} [Fintype A] [Fintype B] [Fintype R]

/-- Kraus maps of `1 ⊗ K` commute with amplification on the left factor. -/
theorem conj_one_kronecker_amplify_apply [DecidableEq A] [DecidableEq B] (K : Matrix S R ℂ)
    (Φ : MatrixMap A B)
    (Z : Matrix (A × R) (A × R) ℂ) :
    conj ((1 : Matrix B B ℂ) ⊗ₖ K) (Φ.amplify R Z) =
      Φ.amplify S (conj ((1 : Matrix A A ℂ) ⊗ₖ K) Z) := by
  rw [← amplifyLeft_conj, ← amplifyLeft_conj, ← LinearMap.comp_apply,
    ← amplify_comp_amplifyLeft, LinearMap.comp_apply]

/-- The trace of a Kraus map of `X ⊗ 1` is the trace of the Kraus map of `X` on the partial
trace. -/
theorem trace_conj_kronecker_one_apply [DecidableEq R] (X : Matrix B A ℂ)
    (Z : Matrix (A × R) (A × R) ℂ) :
    (conj (X ⊗ₖ (1 : Matrix R R ℂ)) Z).trace = (conj X (traceRight A R Z)).trace := by
  rw [← amplify_conj, ← trace_traceRight, ← LinearMap.comp_apply, traceRight_comp_amplify,
    LinearMap.comp_apply]

end tensor

/-- The Kraus map of a matrix moved along a bijection of its basis moves the input back, applies
the Kraus map of the matrix, and moves the result forward. -/
theorem conj_reindex_apply {m n : Type*} [Fintype m] [Fintype n] (e : m ≃ n)
    (M : Matrix m m ℂ) (ρ : Matrix n n ℂ) :
    MatrixMap.conj (Matrix.reindex e e M) ρ =
      (M * ρ.submatrix e e * Mᴴ).submatrix e.symm e.symm := by
  rw [MatrixMap.conj_apply, Matrix.conjTranspose_reindex, Matrix.reindex_apply,
    Matrix.reindex_apply]
  have h : ρ = (ρ.submatrix e e).submatrix e.symm e.symm := by simp
  conv_lhs => rw [h]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

section projectors

variable {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]

/-- Conjugating a supported Hermitian matrix by a conjugated projection multiplies its trace
by the overlap factor of the two projections. -/
theorem trace_re_conj_one_kronecker_eq {C P : Matrix S S ℂ} (hC : Cᴴ = C) (hCC : C * C = 1)
    (hP : Pᴴ = P) (hPP : P * P = P)
    {a : ℝ} (ha : P * (C * P * C) * P = (a : ℂ) • P) {φ : Matrix (B × S) (B × S) ℂ}
    (hφ : φ.IsHermitian) (hφP : ((1 : Matrix B B ℂ) ⊗ₖ P) * φ = φ) :
    a * φ.trace.re =
      (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) φ).trace.re := by
  have hφPr : φ * ((1 : Matrix B B ℂ) ⊗ₖ P) = φ := by
    have h := congrArg conjTranspose hφP
    rwa [conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one, hP,
      hφ.eq] at h
  set Q := (1 : Matrix B B ℂ) ⊗ₖ (C * P * C) with hQ
  have hQH : Qᴴ = Q := by
    rw [hQ, conjTranspose_kronecker, conjTranspose_one, conjTranspose_mul, conjTranspose_mul, hC,
      hP, Matrix.mul_assoc]
  have hQQ : Q * Q = Q := by
    rw [hQ, ← mul_kronecker_mul, Matrix.one_mul]
    congr 1
    rw [show C * P * C * (C * P * C) = C * P * (C * C) * P * C by simp only [Matrix.mul_assoc],
      hCC, Matrix.mul_one, Matrix.mul_assoc C P P, hPP]
  -- the trace of the Kraus map is the trace of `Q φ`
  have h1 : (MatrixMap.conj Q φ).trace = (Q * φ).trace := by
    rw [MatrixMap.conj_apply, hQH, Matrix.trace_mul_cycle, hQQ]
  have h2 : (((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) * φ).trace = (a : ℂ) * φ.trace := by
    calc (((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) * φ).trace
        = (((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) *
            (((1 : Matrix B B ℂ) ⊗ₖ P) * φ * ((1 : Matrix B B ℂ) ⊗ₖ P))).trace := by
          rw [hφP, hφPr]
      _ = ((((1 : Matrix B B ℂ) ⊗ₖ P) * ((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) *
            ((1 : Matrix B B ℂ) ⊗ₖ P)) * φ).trace := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
          simp only [Matrix.mul_assoc]
      _ = (a : ℂ) * φ.trace := by
          rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul, ha,
            kronecker_smul, smul_mul_assoc, trace_smul, hφP, smul_eq_mul]
  rw [h1, h2]
  simp

/-- `trace_re_conj_one_kronecker_eq` for a Hermitian matrix fixed by conjugation with `Q`,
where `P Q = Q`: the hypothesis `(1 ⊗ P) φ = φ` follows from `(1 ⊗ Q) φ (1 ⊗ Q)ᴴ = φ`. -/
theorem trace_re_conj_one_kronecker_eq_of_conj {C P Q : Matrix S S ℂ} (hC : Cᴴ = C)
    (hCC : C * C = 1) (hP : Pᴴ = P) (hPP : P * P = P) {a : ℝ}
    (ha : P * (C * P * C) * P = (a : ℂ) • P) (hPQ : P * Q = Q)
    {φ : Matrix (B × S) (B × S) ℂ} (hφ : φ.IsHermitian)
    (hφQ : MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ Q) φ = φ) :
    a * φ.trace.re =
      (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) φ).trace.re := by
  refine trace_re_conj_one_kronecker_eq hC hCC hP hPP ha hφ ?_
  rw [← hφQ, MatrixMap.conj_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← mul_kronecker_mul,
    Matrix.one_mul, hPQ]

/-- Composing the Kraus maps of `1 ⊗ C D_p C` and then `1 ⊗ C D_q C`, for diagonal projectors
`D_p`, `D_q` and an involution `C`, gives the Kraus map of `1 ⊗ C D_{p ∧ q} C`. -/
theorem conj_one_kronecker_comp_conj_one_kronecker {C : Matrix S S ℂ} (hCC : C * C = 1)
    (p q : S → Prop) [DecidablePred p] [DecidablePred q] :
    MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
      (C * diagonal (fun d ↦ if q d then 1 else 0) * C)) ∘ₗ
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
          (C * diagonal (fun d ↦ if p d then 1 else 0) * C)) =
      MatrixMap.conj
        ((1 : Matrix B B ℂ) ⊗ₖ
          (C * diagonal (fun d ↦ if p d ∧ q d then 1 else 0) * C)) := by
  rw [← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul]
  congr 2
  rw [show C * diagonal (fun d ↦ if q d then (1 : ℂ) else 0) * C *
      (C * diagonal (fun d ↦ if p d then 1 else 0) * C) =
      C * diagonal (fun d ↦ if q d then (1 : ℂ) else 0) * (C * C) *
        diagonal (fun d ↦ if p d then 1 else 0) * C by simp only [Matrix.mul_assoc],
    hCC, Matrix.mul_one, Matrix.mul_assoc C, diagonal_mul_diagonal]
  congr 3
  funext d
  by_cases hp : p d <;> by_cases hq : q d <;> simp [hp, hq]

/-- The Kraus map of `1 ⊗ C D C` for the full diagonal projector and an involution `C` is the
identity. -/
theorem conj_one_kronecker_true {C : Matrix S S ℂ} (hCC : C * C = 1) :
    MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (C * diagonal (fun _ : S ↦ if True then (1 : ℂ) else 0) * C)) = LinearMap.id := by
  simp only [↓reduceIte, diagonal_one, Matrix.mul_one, hCC, one_kronecker_one, MatrixMap.conj_one]

end projectors

end Quantum.MatrixMap
