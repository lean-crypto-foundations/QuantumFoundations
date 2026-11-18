/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import QuantumFoundations.ForMathlib.Data.Matrix.Composition

/-!
# Positivity of C⋆-matrices of complex matrices

A Mathlib candidate for `Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean`. With the L2 operator
norm, `Matrix n n ℂ` is a C⋆-algebra ordered by the Loewner order, and `CStarMatrix k k` of it
carries the spectral order. A C⋆-matrix of matrices is nonnegative exactly when the flattened
matrix on `k × n` is positive semidefinite.

## Main results

* `CStarMatrix.nonneg_iff_posSemidef_comp` — `0 ≤ M` iff `Matrix.comp` of `M` is positive
  semidefinite.
-/

@[expose] public section

set_option autoImplicit false

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace CStarMatrix

variable {k n : Type*} [Fintype k] [Fintype n] [DecidableEq n]

/-- A C⋆-matrix of complex matrices is nonnegative in the spectral order iff its flattening by
`Matrix.comp` is positive semidefinite. -/
theorem nonneg_iff_posSemidef_comp (M : CStarMatrix k k (Matrix n n ℂ)) :
    0 ≤ M ↔ (Matrix.comp k k n n ℂ (ofMatrix.symm M)).PosSemidef := by
  classical
  let e : CStarMatrix k k (Matrix n n ℂ) ≃⋆ₐ[ℂ] Matrix (k × n) (k × n) ℂ :=
    ofMatrixStarAlgEquiv.symm.trans (Matrix.compStarAlgEquiv k n ℂ ℂ)
  have he : (0 ≤ e M) ↔ 0 ≤ M := by
    simpa only [map_zero] using map_le_map_iff e (a := 0) (b := M)
  rw [← he, Matrix.nonneg_iff_posSemidef]
  rfl

end CStarMatrix
