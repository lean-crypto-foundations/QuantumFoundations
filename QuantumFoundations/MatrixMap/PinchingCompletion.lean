/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.MatrixMap.Commutant
public import QuantumFoundations.MatrixMap.Completion

/-!
# Localized matrix completion
-/

public section

open scoped Matrix.Norms.L2Operator Kronecker ComplexConjugate

namespace Matrix

/-- Complete the rows and columns that change a label, then localize the completion to
invariant blocks. The resulting approximation preserves the labels. -/
theorem exists_pinch_eq_sub_sq_le_of_completion
    {n κ Λ : Type*} [Fintype n] [DecidableEq n] [DecidableEq κ]
    (β : n → κ) (γ : n → Λ) (bad : n → Prop) [DecidablePred bad]
    (A : Matrix n n ℂ) (d : n → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hrow : ‖diagonal (fun i ↦ if bad i then (1 : ℂ) else 0) * (A - diagonal d)‖ ≤ √c)
    (hcol : ‖(A - diagonal d) * diagonal (fun i ↦ if bad i then (1 : ℂ) else 0)‖ ≤ √c)
    (hblock : ∀ i j, A i j ≠ 0 → i ≠ j → γ i = γ j)
    (hgood : ∀ i j, γ i = γ j → i ≠ j → ¬bad i → ¬bad j → β i = β j) :
    ∃ S, pinch β S = S ∧ ‖A - S‖ ^ 2 ≤ c := by
  classical
  let P : Matrix n n ℂ := diagonal (fun i ↦ if bad i then 1 else 0)
  have hP : IsStarProjection P := by
    refine ⟨?_, ?_⟩
    · dsimp [P]
      rw [IsIdempotentElem, diagonal_mul_diagonal]
      congr 1
      funext i
      split_ifs <;> simp
    · dsimp only [P]
      rw [IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
      congr 1
      funext i
      split_ifs <;> simp_all
  obtain ⟨T, hPT, hTP, hT⟩ := exists_completion hP hrow hcol
  have hr : ∀ i j, bad i → T i j = (A - diagonal d) i j := by
    intro i j hi
    have h := congrFun (congrFun hPT i) j
    simpa [P, diagonal_mul, hi] using h
  have hl : ∀ i j, bad j → T i j = (A - diagonal d) i j := by
    intro i j hj
    have h := congrFun (congrFun hTP i) j
    simpa [P, mul_diagonal, hj] using h
  refine ⟨A - pinch γ T, ?_, ?_⟩
  · rw [pinch_eq_self_iff]
    intro i j hij
    by_cases he : i = j
    · simp [he]
    rw [Matrix.sub_apply, pinch_apply] at hij
    by_cases hg : γ i = γ j
    · rw [ite_eq_left hg] at hij
      have hi : ¬bad i := by
        intro hi
        simp [hr i j hi, Matrix.sub_apply, diagonal_apply_ne _ he] at hij
      have hj : ¬bad j := by
        intro hj
        simp [hl i j hj, Matrix.sub_apply, diagonal_apply_ne _ he] at hij
      exact hgood i j hg he hi hj
    · rw [ite_eq_right hg, sub_zero] at hij
      exact False.elim (hg (hblock i j hij he))
  · rw [sub_sub_cancel]
    exact (pow_le_pow_left₀ (norm_nonneg _) ((l2_opNorm_pinch_le γ T).trans hT) 2).trans_eq
      (Real.sq_sqrt hc)

/-- A label-controlled operator of scalars is diagonal. -/
theorem labelControlled_smul_one {n κ : Type*} [DecidableEq n] (β : n → κ) (c : κ → ℂ) :
    labelControlled β (fun k ↦ c k • (1 : Matrix n n ℂ)) = diagonal fun a ↦ c (β a) := by
  ext a b
  rw [labelControlled_apply, Matrix.smul_apply, one_apply, diagonal_apply]
  split_ifs <;> simp

end Matrix
