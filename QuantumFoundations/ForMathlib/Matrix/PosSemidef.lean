/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.ForMathlib.Analysis.Matrix.PosSemidef
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Block positivity and quadratic forms
-/

public section

open scoped ComplexOrder ComplexConjugate InnerProductSpace

namespace Matrix

/-- A Hermitian matrix whose quadratic form has nonnegative real part is positive semidefinite. -/
theorem posSemidef_of_re_dotProduct_mulVec_nonneg {n : Type*} [Fintype n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian)
    (h : ∀ x : n → ℂ, 0 ≤ (star x ⬝ᵥ (M *ᵥ x)).re) : M.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg hM fun x ↦ ?_
  have him : (star x ⬝ᵥ (M *ᵥ x)).im = 0 :=
    Complex.conj_eq_iff_im.mp (hM.star_dotProduct_mulVec_comm x x)
  exact Complex.nonneg_iff.mpr ⟨h x, him.symm⟩

/-- A block-diagonal matrix of positive semidefinite blocks, over a sigma type, is positive
semidefinite. The set of blocks and the blocks themselves can be infinite. -/
theorem posSemidef_blockDiagonal' {o : Type*} [DecidableEq o] {m : o → Type*}
    {M : ∀ k, Matrix (m k) (m k) ℂ} (hM : ∀ k, (M k).PosSemidef) :
    (blockDiagonal' M).PosSemidef := by
  classical
  refine ⟨?_, fun x ↦ ?_⟩
  · rw [IsHermitian, blockDiagonal'_conjTranspose]
    exact congrArg blockDiagonal' (funext fun k ↦ (hM k).1)
  · have hrow (k : o) (i : m k) (xi : ℂ) :
        x.sum (fun j xj ↦ star xi * blockDiagonal' M ⟨k, i⟩ j * xj) =
          (x.split k).sum (fun j xj ↦ star xi * M k i j * xj) := by
      rw [Finsupp.sigma_sum, Finset.sum_eq_single k]
      · simp only [blockDiagonal'_apply_eq]
      · intro l _ hl
        simp [blockDiagonal'_apply_ne _ _ _ (Ne.symm hl)]
      · intro hk
        have hz : x.split k = 0 := by
          simpa only [Finsupp.mem_splitSupport_iff_nonzero, not_not] using hk
        simp [hz]
    rw [Finsupp.sigma_sum]
    simp_rw [hrow]
    exact Finset.sum_nonneg fun k _ ↦ (hM k).2 (x.split k)

/-- A block-diagonal matrix of positive semidefinite blocks is positive semidefinite.
Neither the set of blocks nor their common index type needs to be finite. -/
theorem posSemidef_blockDiagonal {m o : Type*} [DecidableEq o]
    {M : o → Matrix m m ℂ} (hM : ∀ k, (M k).PosSemidef) : (blockDiagonal M).PosSemidef := by
  have h := (posSemidef_blockDiagonal' hM).submatrix (fun p : m × o ↦ (⟨p.2, p.1⟩ : Σ _ : o, m))
  convert h using 1
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases hkl : k = l
  · subst l
    simp
  · simp [blockDiagonal_apply, blockDiagonal'_apply_ne _ _ _ hkl, hkl]

/-- **Bessel's inequality for two orthonormal vectors**, in coordinates. -/
theorem norm_dotProduct_star_sq_add_le {n : Type*} [Fintype n] {e₁ e₂ : n → ℂ}
    (h₁ : e₁ ⬝ᵥ star e₁ = 1)
    (h₂ : e₂ ⬝ᵥ star e₂ = 1) (h₁₂ : e₂ ⬝ᵥ star e₁ = 0) (φ : n → ℂ) :
    ‖φ ⬝ᵥ star e₁‖ ^ 2 + ‖φ ⬝ᵥ star e₂‖ ^ 2 ≤ ∑ i, ‖φ i‖ ^ 2 := by
  have h₂₁ : e₁ ⬝ᵥ star e₂ = 0 := by rw [dotProduct_star, h₁₂, star_zero]
  let v : Fin 2 → EuclideanSpace ℂ n := ![WithLp.toLp 2 e₁, WithLp.toLp 2 e₂]
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    simp only [Fin.forall_fin_two, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      EuclideanSpace.inner_toLp_toLp, h₁, h₂, h₁₂, h₂₁]
    simp
  have := hv.sum_inner_products_le (x := WithLp.toLp 2 φ) (s := Finset.univ)
  simpa [Fin.sum_univ_two, v, EuclideanSpace.inner_toLp_toLp, EuclideanSpace.norm_sq_eq]
    using this

/-- A block-diagonal matrix of unitaries is unitary. -/
theorem blockDiagonal'_mem_unitaryGroup {o : Type*} [Fintype o] [DecidableEq o]
    {m : o → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {M : ∀ i, Matrix (m i) (m i) ℂ}
    (hM : ∀ i, M i ∈ Matrix.unitaryGroup (m i) ℂ) :
    Matrix.blockDiagonal' M ∈ Matrix.unitaryGroup (Σ i, m i) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simp_rw [← Matrix.star_eq_conjTranspose, fun i ↦ Matrix.mem_unitaryGroup_iff'.mp (hM i)]
  exact Matrix.blockDiagonal'_one

/-- The trace of `C |v⟩⟨v| C†` is the squared norm of `C v`. -/
theorem trace_mul_vecMulVec_mul_conjTranspose_re {m n : Type*} [Fintype m] [Fintype n]
    (C : Matrix n m ℂ) (v : m → ℂ) :
    (C * vecMulVec v (star v) * Cᴴ).trace.re = ∑ a, ‖(C *ᵥ v) a‖ ^ 2 := by
  rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec, trace_vecMulVec]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.re_sum,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end Matrix
