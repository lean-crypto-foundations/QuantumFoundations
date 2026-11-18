/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import QuantumFoundations.ForMathlib.Analysis.CStarAlgebra.CStarMatrix
public import QuantumFoundations.MatrixMap

/-!
# Completely positive matrix maps as completely positive maps of C⋆-algebras

QuantumFoundations' `Quantum.MatrixMap.IsCP` and Mathlib's `CompletelyPositiveMap` agree on
linear maps `Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ`, where `Matrix n n ℂ` carries the L2 operator norm
C⋆-algebra structure and the Loewner order.

`Quantum.MatrixMap.amplify` places the reference index on the right (`A × R`); Mathlib's
`CStarMatrix.map` and `Matrix.comp` place it on the left (`R × A`). The two are related by
reindexing along `Prod.swap` (`Quantum.MatrixMap.amplify_submatrix_swap`).

## Main results

* `Quantum.MatrixMap.isCP_iff_map_cstarMatrix_nonneg` — `IsCP` is the condition in the
  definition of `CompletelyPositiveMap`.
* `Quantum.MatrixMap.IsCP.toCompletelyPositiveMap` — a completely positive matrix map, bundled.
* `CompletelyPositiveMap.isCP_toLinearMap` — the underlying linear map of a bundled completely
  positive map of matrix algebras is `IsCP`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator CStarAlgebra

namespace Quantum.MatrixMap

variable {A B : Type*}

/-- Amplification on the right, conjugated by the swap of the two index factors, is the
entrywise map of a block matrix flattened with the reference index on the left. -/
theorem amplify_submatrix_swap (Φ : MatrixMap A B) {R : Type*}
    (M : Matrix R R (Matrix A A ℂ)) :
    (Φ.amplify R ((Matrix.comp R R A A ℂ M).submatrix Prod.swap Prod.swap)).submatrix
        Prod.swap Prod.swap = Matrix.comp R R B B ℂ (M.map Φ) := by
  ext x y
  rfl

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- QuantumFoundations' complete positivity is the condition defining Mathlib's
`CompletelyPositiveMap`: entrywise application preserves nonnegativity of `k × k`
C⋆-matrices for every `k`. -/
theorem isCP_iff_map_cstarMatrix_nonneg (Φ : MatrixMap A B) :
    Φ.IsCP ↔ ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (Matrix A A ℂ)),
      0 ≤ M → 0 ≤ M.map Φ := by
  constructor
  · intro hΦ k M hM
    rw [CStarMatrix.nonneg_iff_posSemidef_comp] at hM ⊢
    have hρ : ((Matrix.comp (Fin k) (Fin k) A A ℂ (CStarMatrix.ofMatrix.symm M)).submatrix
        (Equiv.prodComm A (Fin k)) (Equiv.prodComm A (Fin k))).PosSemidef :=
      (Matrix.posSemidef_submatrix_equiv _).mpr hM
    have h := hΦ k _ hρ
    rw [← Matrix.posSemidef_submatrix_equiv (Equiv.prodComm (Fin k) B)] at h
    exact amplify_submatrix_swap Φ (CStarMatrix.ofMatrix.symm M) ▸ h
  · intro h k ρ hρ
    let N : Matrix (Fin k) (Fin k) (Matrix A A ℂ) :=
      (Matrix.comp (Fin k) (Fin k) A A ℂ).symm (ρ.submatrix Prod.swap Prod.swap)
    have hN : 0 ≤ CStarMatrix.ofMatrix N := by
      rw [CStarMatrix.nonneg_iff_posSemidef_comp]
      simpa [N] using (Matrix.posSemidef_submatrix_equiv (Equiv.prodComm (Fin k) A)).mpr hρ
    have hmap := h k _ hN
    rw [CStarMatrix.nonneg_iff_posSemidef_comp] at hmap
    have hcomp : (Matrix.comp (Fin k) (Fin k) A A ℂ N).submatrix Prod.swap Prod.swap = ρ := by
      ext x y
      rfl
    have key := amplify_submatrix_swap Φ N
    rw [hcomp] at key
    refine (Matrix.posSemidef_submatrix_equiv (M := Φ.amplify (Fin k) ρ)
      (Equiv.prodComm (Fin k) B)).mp ?_
    rw [Equiv.coe_prodComm (Fin k) B, key]
    exact hmap

/-- A completely positive matrix map as a bundled completely positive map of C⋆-algebras. -/
def IsCP.toCompletelyPositiveMap {Φ : MatrixMap A B} (hΦ : Φ.IsCP) :
    Matrix A A ℂ →CP Matrix B B ℂ where
  toLinearMap := Φ
  map_cstarMatrix_nonneg' := (isCP_iff_map_cstarMatrix_nonneg Φ).mp hΦ

/-- The linear map underlying `IsCP.toCompletelyPositiveMap` is the given matrix map. -/
@[simp]
theorem IsCP.toLinearMap_toCompletelyPositiveMap {Φ : MatrixMap A B} (hΦ : Φ.IsCP) :
    hΦ.toCompletelyPositiveMap.toLinearMap = Φ := rfl

end Quantum.MatrixMap

namespace CompletelyPositiveMap

open Quantum

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The linear map underlying a completely positive map of matrix algebras is completely positive
in the sense of `Quantum.MatrixMap.IsCP`. -/
theorem isCP_toLinearMap (φ : Matrix A A ℂ →CP Matrix B B ℂ) :
    MatrixMap.IsCP φ.toLinearMap :=
  (MatrixMap.isCP_iff_map_cstarMatrix_nonneg _).mpr φ.map_cstarMatrix_nonneg'

end CompletelyPositiveMap
