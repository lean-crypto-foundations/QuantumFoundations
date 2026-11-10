/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.KroneckerPSD
public import Mathlib.Analysis.Matrix.Order

/-!
# Matrix contractions and tensor identities
-/

public section

open scoped Kronecker ComplexOrder

namespace Matrix

/-- A product of contractions is a contraction. -/
theorem posSemidef_one_sub_mul {l m n : Type*} [Fintype l] [Fintype m] [Finite n]
    [DecidableEq m] [DecidableEq n] {K : Matrix l m ℂ} {L : Matrix m n ℂ}
    (hK : (1 - Kᴴ * K).PosSemidef) (hL : (1 - Lᴴ * L).PosSemidef) :
    (1 - (K * L)ᴴ * (K * L)).PosSemidef := by
  have h : 1 - (K * L)ᴴ * (K * L) = (1 - Lᴴ * L) + Lᴴ * (1 - Kᴴ * K) * L := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    abel
  rw [h]
  exact hL.add (hK.conjTranspose_mul_mul_same L)

/-- `1 ⊗ X` is a contraction when `X` is. -/
theorem posSemidef_one_sub_one_kronecker {k m n : Type*} [Fintype k] [DecidableEq k] [Fintype m]
    [Finite n] [DecidableEq n] {X : Matrix m n ℂ}
    (h : (1 - Xᴴ * X).PosSemidef) :
    (1 - ((1 : Matrix k k ℂ) ⊗ₖ X)ᴴ * ((1 : Matrix k k ℂ) ⊗ₖ X)).PosSemidef := by
  have e : 1 - ((1 : Matrix k k ℂ) ⊗ₖ X)ᴴ * ((1 : Matrix k k ℂ) ⊗ₖ X) =
      (1 : Matrix k k ℂ) ⊗ₖ (1 - Xᴴ * X) := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    ext ⟨a, b⟩ ⟨a', b'⟩
    by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]
  rw [e]
  exact Matrix.PosSemidef.one.kronecker h

/-- `P ⊗ 1` is a contraction when `P` is. -/
theorem posSemidef_one_sub_kronecker_one {m n k : Type*} [Fintype m] [Fintype k]
    [Finite n] [DecidableEq n] [DecidableEq k] {P : Matrix m n ℂ} (hP : (1 - Pᴴ * P).PosSemidef) :
    (1 - (P ⊗ₖ (1 : Matrix k k ℂ))ᴴ * (P ⊗ₖ (1 : Matrix k k ℂ))).PosSemidef := by
  have e : 1 - (P ⊗ₖ (1 : Matrix k k ℂ))ᴴ * (P ⊗ₖ (1 : Matrix k k ℂ)) =
      (1 - Pᴴ * P) ⊗ₖ (1 : Matrix k k ℂ) := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    ext ⟨a, b⟩ ⟨a', b'⟩
    by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]
  rw [e]
  exact hP.kronecker Matrix.PosSemidef.one

/-- If `K * Kᴴ = 1`, then `Kᴴ * K` is a projector, so `1 - Kᴴ * K` is positive semidefinite. -/
theorem posSemidef_one_sub_conjTranspose_mul_self {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m]
    [DecidableEq n]
    {K : Matrix m n ℂ} (hK : K * Kᴴ = 1) : (1 - Kᴴ * K).PosSemidef := by
  have hQ : Kᴴ * K * (Kᴴ * K) = Kᴴ * K := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc K, hK, Matrix.one_mul]
  have h : (1 - Kᴴ * K)ᴴ * (1 - Kᴴ * K) = 1 - Kᴴ * K := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hQ, sub_self, sub_zero]
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

open scoped MatrixOrder in
/-- If `P` is a Hermitian projector and `U` is an isometry, then `P U P` is a contraction:
`1 - (P U P)ᴴ (P U P)` is positive semidefinite. -/
theorem posSemidef_one_sub_conjTranspose_mul_self_of_projector {n : Type*} [Fintype n]
    [DecidableEq n] {P U : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P) (hU : Uᴴ * U = 1) :
    (1 - (P * U * P)ᴴ * (P * U * P)).PosSemidef := by
  have hP₁ : (1 - P).PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp
      (show IsStarProjection P from ⟨hPP, hP⟩).one_sub_nonneg
  have e : 1 - (P * U * P)ᴴ * (P * U * P) = (1 - P) + Pᴴ * (Uᴴ * (1 - P) * U) * P := by
    rw [conjTranspose_mul, conjTranspose_mul, hP]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P, hPP, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul, hPP]
    abel
  rw [e]
  exact hP₁.add ((hP₁.conjTranspose_mul_mul_same U).conjTranspose_mul_mul_same P)

/-- `(1 ⊗ V)ᴴ (1 ⊗ V) = 1` for an isometry `V`. -/
theorem conjTranspose_one_kronecker_mul_self {k m n : Type*} [Fintype k] [DecidableEq k] [Fintype m]
    [DecidableEq n] {V : Matrix m n ℂ} (hV : Vᴴ * V = 1) :
    ((1 : Matrix k k ℂ) ⊗ₖ V)ᴴ * ((1 : Matrix k k ℂ) ⊗ₖ V) = 1 := by
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, hV,
    one_kronecker_one]

/-- `(1 ⊗ V) (1 ⊗ Vᴴ) = 1` for a coisometry `V`. -/
theorem one_kronecker_mul_conjTranspose {k m n : Type*} [Fintype k] [DecidableEq k] [Fintype n]
    [DecidableEq m] {V : Matrix m n ℂ} (hV : V * Vᴴ = 1) :
    ((1 : Matrix k k ℂ) ⊗ₖ V) * ((1 : Matrix k k ℂ) ⊗ₖ V)ᴴ = 1 := by
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, hV,
    one_kronecker_one]

/-- `A ⊗ 1` and `1 ⊗ X` commute: both products are `A ⊗ X`. -/
theorem kronecker_one_mul_one_kronecker {m n p q : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] [Fintype m] [DecidableEq m] [Fintype q] [DecidableEq q]
    (A : Matrix m n ℂ) (X : Matrix p q ℂ) :
    (A ⊗ₖ (1 : Matrix p p ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ X) =
      ((1 : Matrix m m ℂ) ⊗ₖ X) * (A ⊗ₖ (1 : Matrix q q ℂ)) := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one]

section
variable {l m n n' : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype n']

/-- Sending a block into a block is preserved by a left factor that intertwines the blocks of
the output. -/
theorem mul_mul_eq_of_comm_left {Bo : Matrix l l ℂ} {L : Matrix l m ℂ} {Bm : Matrix m m ℂ}
    {F : Matrix m n ℂ} {Bi : Matrix n n ℂ} (hL : Bo * L = L * Bm) (h : Bm * F * Bi = F * Bi) :
    Bo * (L * F) * Bi = L * F * Bi := by
  calc Bo * (L * F) * Bi = L * (Bm * F * Bi) := by
        rw [← Matrix.mul_assoc, hL]
        simp only [Matrix.mul_assoc]
    _ = L * F * Bi := by rw [h, Matrix.mul_assoc]

/-- Sending a block into a block is preserved by a right factor that intertwines the blocks of
the input. -/
theorem mul_mul_eq_of_comm_right {Bo : Matrix m m ℂ} {F : Matrix m n ℂ} {Bi : Matrix n n ℂ}
    {R : Matrix n n' ℂ} {Bi' : Matrix n' n' ℂ} (hR : R * Bi' = Bi * R)
    (h : Bo * F * Bi = F * Bi) : Bo * (F * R) * Bi' = F * R * Bi' := by
  calc Bo * (F * R) * Bi' = Bo * F * Bi * R := by simp only [Matrix.mul_assoc, hR]
    _ = F * R * Bi' := by rw [h]; simp only [Matrix.mul_assoc, hR]

end

/-- A block of a matrix conjugated by `1 ⊗ C` is the block conjugated by `C`. -/
theorem submatrix_one_kronecker_mul_mul_one_kronecker {A S : Type*} [Fintype A] [DecidableEq A]
    [Fintype S] (C : Matrix S S ℂ) (M : Matrix (A × S) (A × S) ℂ) (a b : A) :
    (((1 : Matrix A A ℂ) ⊗ₖ C) * M * ((1 : Matrix A A ℂ) ⊗ₖ C)).submatrix
        (fun d ↦ (a, d))
        (fun d ↦ (b, d)) =
      C * M.submatrix (fun d ↦ (a, d)) (fun d ↦ (b, d)) * C := by
  ext d d'
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_mul,
    ite_mul, mul_ite]

/-- A diagonal `0/1` matrix is Hermitian. -/
theorem conjTranspose_diagonal_ite {S : Type*} [DecidableEq S] (p : S → Prop) [DecidablePred p] :
    (diagonal fun d ↦ if p d then (1 : ℂ) else 0)ᴴ =
      diagonal fun d ↦ if p d then 1 else 0 := by
  rw [diagonal_conjTranspose]
  congr 1
  funext d
  by_cases h : p d <;> simp [h]

/-- The product of two diagonal `0/1` matrices is the diagonal `0/1` matrix of the
conjunction. -/
theorem diagonal_ite_mul_diagonal_ite {S : Type*} [DecidableEq S] [Fintype S] (p q : S → Prop)
    [DecidablePred p] [DecidablePred q] :
    (diagonal fun d ↦ if p d then (1 : ℂ) else 0) * (diagonal fun d ↦ if q d then 1 else 0) =
      diagonal fun d ↦ if p d ∧ q d then 1 else 0 := by
  rw [diagonal_mul_diagonal]
  congr 1
  funext d
  by_cases hp : p d <;> by_cases hq : q d <;> simp [hp, hq]

/-- A diagonal `0/1` matrix is idempotent. -/
theorem diagonal_ite_mul_self {S : Type*} [DecidableEq S] [Fintype S] (p : S → Prop)
    [DecidablePred p] :
    (diagonal fun d ↦ if p d then (1 : ℂ) else 0) * (diagonal fun d ↦ if p d then 1 else 0) =
      diagonal fun d ↦ if p d then 1 else 0 := by
  rw [diagonal_ite_mul_diagonal_ite]
  simp only [and_self]

/-- An entry of `(1 ⊗ A) diag(d) (1 ⊗ B)`: the first register is kept, and the second is
summed over the intermediate states. -/
theorem one_kronecker_mul_diagonal_mul_one_kronecker_apply {Q Z : Type*} [Fintype Q]
    [DecidableEq Q] [Fintype Z] [DecidableEq Z] (A B : Matrix Z Z ℂ) (d : Q × Z → ℂ)
    (q' : Q) (z' : Z) (q : Q) (z : Z) :
    (((1 : Matrix Q Q ℂ) ⊗ₖ A) * diagonal d * ((1 : Matrix Q Q ℂ) ⊗ₖ B)) (q', z') (q, z) =
      if q' = q then ∑ z₁, A z' z₁ * d (q, z₁) * B z₁ z else 0 := by
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single q]
  · simp only [mul_diagonal, kroneckerMap_apply, one_apply, ↓reduceIte, one_mul]
    split_ifs with h
    · subst h
      simp only [one_mul]
    · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- Conjugating twice by a self-adjoint unitary fixes every operator. -/
theorem conjugate_involution {A : Type*} [Fintype A] [DecidableEq A] (V U : Matrix A A ℂ)
    (hv : Vᴴ = V) (hV : Vᴴ * V = 1) :
    Vᴴ * (Vᴴ * U * V) * V = U := by
  have hh : V * V = 1 := by rwa [hv] at hV
  rw [hv]
  calc
    V * (V * U * V) * V = (V * V) * U * (V * V) := by simp only [Matrix.mul_assoc]
    _ = U := by rw [hh, Matrix.one_mul, Matrix.mul_one]

end Matrix

/-- Multiplying conjugates cancels the interior copies of an involution. -/
theorem conj_mul_conj_of_involution {M : Type*} [Monoid M] (C : M) (hC : C * C = 1) (P Q : M) :
    (C * P * C) * (C * Q * C) = C * (P * Q) * C := by
  calc
    _ = C * P * (C * C) * Q * C := by simp only [mul_assoc]
    _ = _ := by rw [hC, mul_one]; simp only [mul_assoc]

/-- Conjugation by an involution preserves commutation. -/
theorem conj_comm_of_involution {M : Type*} [Monoid M] {P A B : M} (hP : P * P = 1)
    (h : A * B = B * A) : P * A * P * (P * B * P) = P * B * P * (P * A * P) := by
  rw [conj_mul_conj_of_involution P hP, conj_mul_conj_of_involution P hP, h]
