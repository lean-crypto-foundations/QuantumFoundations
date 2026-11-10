/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.MatrixMap.BlockNorm
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Norm bounds for blocks and restrictions
-/

public section

open scoped Matrix.Norms.L2Operator Kronecker ComplexOrder

namespace Matrix

/-- A block-diagonal matrix has norm at most `r` when every block does. -/
theorem l2_opNorm_blockDiagonal_le {o m : Type*} [Fintype o] [DecidableEq o]
    [Fintype m] [DecidableEq m] (F : o → Matrix m m ℂ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ c, ‖F c‖ ≤ r) : ‖blockDiagonal F‖ ≤ r := by
  have he : blockDiagonal F = (∑ c, single c c (1 : ℂ) ⊗ₖ F c).submatrix
      (Equiv.prodComm m o) (Equiv.prodComm m o) := by
    ext ⟨a, c⟩ ⟨b, c'⟩
    rw [submatrix_apply, Equiv.prodComm_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Prod.swap_prod_mk, sum_single_kronecker_apply, blockDiagonal_apply]
  rw [he, l2_opNorm_submatrix_equiv, l2_opNorm_sum_single_kronecker]
  exact Real.iSup_le h hr

/-- **The trace bound through a block-diagonal operator on a projected state.** If `C Q` agrees
with `(⊕_c F c) Q` after reindexing by `e`, every block has `‖F c‖² ≤ r`, and the positive
semidefinite `σ` is fixed by conjugation with `Q`, then `tr(C σ C†) ≤ r tr σ`. -/
theorem re_trace_mul_mul_conjTranspose_le_of_blockDiagonal {N B o : Type*} [Fintype N]
    [Fintype B] [DecidableEq B] [Finite o] [DecidableEq o] (e : N ≃ B × o)
    (F : o → Matrix B B ℂ) {r : ℝ} (hr : 0 ≤ r) (hF : ∀ c, ‖F c‖ ^ 2 ≤ r)
    {C Q σ : Matrix N N ℂ} (hC : C * Q = (blockDiagonal F).submatrix e e * Q)
    (hσ : Quantum.MatrixMap.conj Q σ = σ) (hpsd : σ.PosSemidef) :
    (C * σ * Cᴴ).trace.re ≤ r * σ.trace.re := by
  classical
  have := Fintype.ofFinite o
  have key : C * σ * Cᴴ = Quantum.MatrixMap.conj ((blockDiagonal F).submatrix e e) σ := by
    calc _ = Quantum.MatrixMap.conj C (Quantum.MatrixMap.conj Q σ) := by rw [hσ]; rfl
      _ = Quantum.MatrixMap.conj ((blockDiagonal F).submatrix e e * Q) σ := by
        rw [← hC, Quantum.MatrixMap.conj_mul]; rfl
      _ = _ := by rw [Quantum.MatrixMap.conj_mul, LinearMap.comp_apply, hσ]
  have hb : ∀ c, ‖F c‖ ≤ √r := fun c ↦ (le_abs_self _).trans (Real.abs_le_sqrt (hF c))
  have hn : ‖(blockDiagonal F).submatrix e e‖ ^ 2 ≤ r := by
    rw [l2_opNorm_submatrix_equiv]
    calc ‖blockDiagonal F‖ ^ 2 ≤ √r ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _)
            (l2_opNorm_blockDiagonal_le F (Real.sqrt_nonneg r) hb) 2
      _ = r := Real.sq_sqrt hr
  rw [key]
  exact (Quantum.MatrixMap.re_trace_conj_le _ hpsd).trans
    (mul_le_mul_of_nonneg_right hn hpsd.trace_re_nonneg)

section
variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
  [DecidableEq n] [DecidableEq n']

/-- Restricting rows and columns and applying a contractive source mask preserves a norm bound. -/
theorem l2_opNorm_submatrix_mul_mask_le (M : Matrix m n ℂ) (f : m' → m) (g : n' → n)
    (hf : Function.Injective f) (hg : Function.Injective g) (p : n' → ℂ)
    (hp : ∀ a, ‖p a‖ ≤ 1) : ‖M.submatrix f g * diagonal p‖ ≤ ‖M‖ := by
  have hd : ‖diagonal p‖ ≤ 1 := by
    rw [l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr hp
  exact ((l2_opNorm_mul _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hd)).trans
    (l2_opNorm_submatrix_le_of_injective M hf hg)

end

end Matrix
