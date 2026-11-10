/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module

public import QuantumFoundations.CPMap
public import QuantumFoundations.MatrixMap.Dual

/-!
# Agreement of the two developments of completely positive maps

The repository contains two developments of linear maps on complex matrices, both in namespace
`Quantum`:

* the `CPMap` layer, for maps `Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ` on one finite basis type `ι`;
* the `MatrixMap` layer, for maps `MatrixMap A B = Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ`
  between arbitrary basis types.

This file proves that the overlapping definitions agree, so that one side can later be defined
through the other.

## The pairs

* **Trace preservation.** `Quantum.IsTP` and `Quantum.MatrixMap.IsTP` are the same predicate.
* **Trace nonincrease.** `Quantum.IsSTP` and `Quantum.MatrixMap.IsTNI` are the same predicate:
  `Re (tr (Φ ρ)) ≤ Re (tr ρ)` for positive semidefinite `ρ`.
* **Complete positivity.** `Quantum.IsCPMap` amplifies by `id_k ⊗ Φ` (`Quantum.tensorIdMap`),
  with the ancilla `Fin k` on the *left* of the index `Fin k × ι`. `Quantum.MatrixMap.IsCP`
  amplifies by `Φ ⊗ id_k` (`Quantum.MatrixMap.amplify`), with the ancilla on the *right* of
  `ι × Fin k`. Swapping the two factors of the index (`Prod.swap`, the function underlying
  `Equiv.prodComm`) turns one amplification into the other, and preserves positive
  semidefiniteness, so the two notions agree.
* **Choi matrices.** The Choi matrix is `Quantum.MatrixMap.choi`, indexed output first: its entry
  at `((i, a), (j, b))` is `Φ (single a b 1) i j`. Choi's theorem for `Quantum.IsCPMap` is
  positive semidefiniteness of this matrix.
* **Trace duals.** `Quantum.dualMap Φ` is `Quantum.MatrixMap.dual Φ`: both are characterised by
  `tr (Φ† Y * X) = tr (Y * Φ X)`. The functoriality of `Quantum.dualMap` follows from that of
  `Quantum.MatrixMap.dual`.
* **Bundled channels.** A `Quantum.CPTPMap ι` is a completely positive and trace-preserving
  `MatrixMap ι ι` in the sense of `MatrixMap`, and every such map gives a
  `Quantum.CPTPMap ι`.

`Quantum.IsPositiveMap` has no counterpart: the `MatrixMap` layer defines no positivity
predicate, only its consequence `Quantum.MatrixMap.IsCP.posSemidef`.

## Main results

* `Quantum.isTP_iff_matrixMap_isTP`, `Quantum.isSTP_iff_isTNI`
* `Quantum.tensorIdMap_submatrix_swap`: `id_k ⊗ Φ` is `Φ ⊗ id_k` conjugated by the swap.
* `Quantum.isCPMap_iff_isCP`, `Quantum.isCPMap_iff_posSemidef_choi`
* `Quantum.matUnit_eq_single`
* `Quantum.dualMap_eq_dual`, `Quantum.dualMap_id`, `Quantum.dualMap_zero`, `Quantum.dualMap_comp`
* `Quantum.CPTPMap.isCP`, `Quantum.CPTPMap.isTP`, `Quantum.CPTPMap.ofMatrixMap`
-/

public section

open scoped ComplexOrder
open Matrix

namespace Quantum

variable {ι : Type*}

/-- `Quantum.IsTP` is `Quantum.MatrixMap.IsTP`. -/
theorem isTP_iff_matrixMap_isTP [Fintype ι] (Φ : MatrixMap ι ι) : IsTP Φ ↔ MatrixMap.IsTP Φ :=
  Iff.rfl

/-- `Quantum.IsSTP` is `Quantum.MatrixMap.IsTNI`. -/
theorem isSTP_iff_isTNI [Fintype ι] (Φ : MatrixMap ι ι) : IsSTP Φ ↔ MatrixMap.IsTNI Φ :=
  Iff.rfl

/-- The matrix unit `matUnit i j` is Mathlib's `Matrix.single i j 1`. -/
theorem matUnit_eq_single [DecidableEq ι] (i j : ι) : matUnit i j = single i j (1 : ℂ) := by
  ext k l
  simp [matUnit_apply, single, eq_comm]

/-- Amplifying on the left, `id_k ⊗ Φ`, is amplifying on the right, `Φ ⊗ id_k`, after swapping
the factors of the index on the input and the output. -/
theorem tensorIdMap_submatrix_swap (Φ : MatrixMap ι ι) (k : ℕ)
    (ρ : Matrix (ι × Fin k) (ι × Fin k) ℂ) :
    tensorIdMap Φ k (ρ.submatrix Prod.swap Prod.swap) =
      (Φ.amplify (Fin k) ρ).submatrix Prod.swap Prod.swap :=
  rfl

/-- Complete positivity with the ancilla on the left (`Quantum.IsCPMap`) is complete positivity
with the ancilla on the right (`Quantum.MatrixMap.IsCP`). -/
theorem isCPMap_iff_isCP (Φ : MatrixMap ι ι) : IsCPMap Φ ↔ MatrixMap.IsCP Φ := by
  constructor
  · intro hΦ k ρ hρ
    have h := (hΦ k _ (hρ.submatrix Prod.swap)).submatrix Prod.swap
    rwa [tensorIdMap_submatrix_swap, submatrix_submatrix, Prod.swap_swap_eq,
      submatrix_id_id] at h
  · intro hΦ k M hM
    have h := (hΦ k _ (hM.submatrix Prod.swap)).submatrix Prod.swap
    rwa [← tensorIdMap_submatrix_swap, submatrix_submatrix, Prod.swap_swap_eq,
      submatrix_id_id] at h

/-- A map that is completely positive with the ancilla on the left is completely positive with
the ancilla on the right. -/
theorem IsCPMap.isCP {Φ : MatrixMap ι ι} (hΦ : IsCPMap Φ) : MatrixMap.IsCP Φ :=
  (isCPMap_iff_isCP Φ).1 hΦ

/-- A map that is completely positive with the ancilla on the right is completely positive with
the ancilla on the left. -/
theorem MatrixMap.IsCP.isCPMap {Φ : MatrixMap ι ι} (hΦ : MatrixMap.IsCP Φ) :
    IsCPMap Φ :=
  (isCPMap_iff_isCP Φ).2 hΦ

/-- **Choi's theorem** for `Quantum.IsCPMap`: a map is completely positive iff its Choi matrix
`Quantum.MatrixMap.choi Φ` is positive semidefinite. -/
theorem isCPMap_iff_posSemidef_choi [Finite ι] [DecidableEq ι] (Φ : MatrixMap ι ι) :
    IsCPMap Φ ↔ (MatrixMap.choi Φ).PosSemidef :=
  (isCPMap_iff_isCP Φ).trans MatrixMap.isCP_iff_posSemidef_choi

section Dual

variable [Fintype ι] [DecidableEq ι]

/-- The trace dual `Quantum.dualMap` is `Quantum.MatrixMap.dual`. -/
theorem dualMap_eq_dual (Φ : MatrixMap ι ι) : dualMap Φ = MatrixMap.dual Φ :=
  MatrixMap.eq_dual_iff.mpr (dual_spec Φ)

/-- The dual of the identity map is the identity. -/
@[simp]
theorem dualMap_id : dualMap (LinearMap.id : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) = LinearMap.id := by
  rw [dualMap_eq_dual, MatrixMap.dual_id]

/-- The dual of the zero map is zero. -/
@[simp]
theorem dualMap_zero : dualMap (0 : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) = 0 := by
  rw [dualMap_eq_dual, MatrixMap.dual_zero]

/-- The dual reverses composition: `(Φ ∘ Ψ)† = Ψ† ∘ Φ†`. -/
theorem dualMap_comp (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) :
    dualMap (Φ ∘ₗ Ψ) = dualMap Ψ ∘ₗ dualMap Φ := by
  simp only [dualMap_eq_dual, MatrixMap.dual_comp]

end Dual

section CPTPMap

variable [Fintype ι] [DecidableEq ι]

/-- The linear map of a CPTP channel is completely positive in the sense of `MatrixMap`. -/
theorem CPTPMap.isCP (Φ : CPTPMap ι) : MatrixMap.IsCP Φ.toLinearMap :=
  Φ.cp.isCP

/-- The linear map of a CPTP channel is trace preserving in the sense of `MatrixMap`. -/
theorem CPTPMap.isTP (Φ : CPTPMap ι) : MatrixMap.IsTP Φ.toLinearMap :=
  Φ.tp

/-- The CPTP channel of a completely positive, trace-preserving `MatrixMap`. -/
@[expose]
def CPTPMap.ofMatrixMap (Φ : MatrixMap ι ι) (hcp : MatrixMap.IsCP Φ)
    (htp : MatrixMap.IsTP Φ) : CPTPMap ι where
  toLinearMap := Φ
  cp := hcp.isCPMap
  tp := htp

/-- The linear map of `CPTPMap.ofMatrixMap Φ hcp htp` is `Φ`. -/
@[simp]
theorem CPTPMap.ofMatrixMap_toLinearMap (Φ : MatrixMap ι ι)
    (hcp : MatrixMap.IsCP Φ) (htp : MatrixMap.IsTP Φ) :
    (CPTPMap.ofMatrixMap Φ hcp htp).toLinearMap = Φ :=
  rfl

end CPTPMap

end Quantum
