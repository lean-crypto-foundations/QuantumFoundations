/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Composition of matrices as a star-algebra equivalence

A Mathlib candidate for `Mathlib/Data/Matrix/Composition.lean`, which bundles `Matrix.comp` as an
algebra equivalence (`Matrix.compAlgEquiv`) but not as a star-algebra equivalence.

## Main definitions

* `Matrix.compStarAlgEquiv` — `Matrix.comp` as a star-algebra equivalence
  `Matrix I I (Matrix J J R) ≃⋆ₐ[K] Matrix (I × J) (I × J) R`.
-/

@[expose] public section

set_option autoImplicit false

namespace Matrix

variable (I J R K : Type*) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [CommSemiring K] [Semiring R] [StarRing R] [Algebra K R]

/-- `Matrix.comp` as a star-algebra equivalence: a block matrix with blocks in `Matrix J J R`
is identified with a matrix indexed by `I × J`, and the conjugate transpose of the block matrix
corresponds to the conjugate transpose of the flattened matrix (`Matrix.conjTranspose_comp'`). -/
def compStarAlgEquiv : Matrix I I (Matrix J J R) ≃⋆ₐ[K] Matrix (I × J) (I × J) R where
  __ := compAlgEquiv I J R K
  map_smul' r M := map_smul (compAlgEquiv I J R K) r M
  map_star' M := (conjTranspose_comp' M).symm

/-- `Matrix.compStarAlgEquiv` applies `Matrix.comp`. -/
@[simp]
theorem compStarAlgEquiv_apply (M : Matrix I I (Matrix J J R)) :
    compStarAlgEquiv I J R K M = comp I I J J R M := rfl

/-- The inverse of `Matrix.compStarAlgEquiv` applies the inverse of `Matrix.comp`. -/
@[simp]
theorem compStarAlgEquiv_symm_apply (M : Matrix (I × J) (I × J) R) :
    (compStarAlgEquiv I J R K).symm M = (comp I I J J R).symm M := rfl

end Matrix
