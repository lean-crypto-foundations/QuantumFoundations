/-
Copyright (c) 2026 Bas Spitters, Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters, Quang Dao
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import QuantumFoundations.MatrixMap.Kraus

/-!
# Unitary Stinespring dilation and purification

`Quantum.MatrixMap.IsCP.exists_stinespring_of_isTP` writes a channel `Φ : M_A → M_B` as
`ρ ↦ tr_E (S ρ S†)` for an isometry `S : ℂ^A → ℂ^B ⊗ ℂ^E`. This file extends the isometry to a
unitary: the input is placed in the larger system `B × E` by a fixed basis embedding, a unitary
acts there, and the environment is discarded. When the input and output systems agree, the
embedding can be `ψ ↦ ψ ⊗ |r⟩` for a fixed ancilla basis state `r`, and the channel becomes
`ρ ↦ tr_E (U (ρ ⊗ |r⟩⟨r|) U†)`.

A purification of a positive semidefinite `ρ` on `A` is a vector `ψ` on `A × A` whose partial
trace over the right factor is `ρ`; it is the Stinespring form of the state, viewed as a map
from the trivial system.

## Conventions

As in `QuantumFoundations.MatrixMap.Kraus`, the environment is the right factor of a product
basis and is discarded by `Quantum.MatrixMap.traceRight`. A basis embedding `j : A → X` is
represented by the matrix `(1 : Matrix X X ℂ).submatrix id j`, whose column at `a` is the basis
vector at `j a`; conjugating by it places an operator on `A` into the block `j(A) × j(A)` of
`M_X`.

## Main results

* `Quantum.MatrixMap.exists_unitary_submatrix_eq`: an isometry `V : ℂ^A → ℂ^X` is the
  restriction of a unitary on `ℂ^X` to the basis vectors `j(A)`, for any injective `j`.
* `Quantum.MatrixMap.exists_unitary_sum_conj_eq`: Kraus operators satisfying the completeness
  relation are the partial trace of a unitary conjugation.
* `Quantum.MatrixMap.IsCP.exists_unitary_of_isTP`: a channel `M_A → M_B` is
  `ρ ↦ tr_E (U (P ρ P†) U†)` with `U` unitary on `B × E`, `E = B × A`, and `P` a basis
  embedding.
* `Quantum.MatrixMap.IsCP.exists_unitary_kronecker_of_isTP`: a channel `M_A → M_A` is
  `ρ ↦ tr_E (U (ρ ⊗ |r⟩⟨r|) U†)` with `E = A × A`.
* `Matrix.PosSemidef.exists_purification`: a positive semidefinite `ρ` on `A` is the partial
  trace of `|ψ⟩⟨ψ|` for a vector `ψ` on `A × A` with `⟨ψ, ψ⟩ = tr ρ`.

## References

* W. F. Stinespring, *Positive functions on C*-algebras*, Proc. Amer. Math. Soc. 6 (1955)
* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018, §2.2
  (Stinespring representations) and §2.1 (purifications).
-/

public section

open scoped Matrix ComplexOrder InnerProductSpace Kronecker
open Matrix

namespace Quantum

namespace MatrixMap

variable {A B X R ι : Type*}

/-! ## Extending an isometry to a unitary -/

/-- An isometry `V : ℂ^A → ℂ^X` extends to a unitary on `ℂ^X`: for any injective `j : A → X`
there is a unitary `U` whose column at `j a` is the column of `V` at `a`. -/
theorem exists_unitary_submatrix_eq [DecidableEq A] [Fintype X] [DecidableEq X]
    {V : Matrix X A ℂ} (hV : Vᴴ * V = 1) {j : A → X} (hj : Function.Injective j) :
    ∃ U ∈ unitaryGroup X ℂ, U.submatrix id j = V := by
  let col : A → EuclideanSpace ℂ X := fun a ↦ WithLp.toLp 2 fun x ↦ V x a
  have hcol : Orthonormal ℂ col := by
    rw [orthonormal_iff_ite]
    intro a a'
    have h := congrFun (congrFun hV a) a'
    rw [mul_apply, one_apply] at h
    rw [← h]
    simp only [col, PiLp.inner_apply, conjTranspose_apply, RCLike.inner_apply]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  let v : X → EuclideanSpace ℂ X := Function.extend j col 0
  have hv : Orthonormal ℂ ((Set.range j).domRestrict v) := by
    have : (Set.range j).domRestrict v = col ∘ (Equiv.ofInjective j hj).symm := by
      funext ⟨_, a, rfl⟩
      simp [v, hj.extend_apply]
    rw [this]
    exact hcol.comp _ (Equiv.injective _)
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨(EuclideanSpace.basisFun X ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun X ℂ).toMatrix_orthonormalBasis_mem_unitary b, ?_⟩
  ext x a
  have hba : b (j a) = col a := by
    rw [hb _ ⟨a, rfl⟩]
    simp [v, hj.extend_apply]
  simpa [Module.Basis.toMatrix_apply] using congrArg (fun w ↦ w.ofLp x) hba

/-- Multiplying by the matrix of a basis embedding selects columns. -/
theorem mul_submatrix_one_id [Fintype X] [DecidableEq X] (U : Matrix X X ℂ) (j : A → X) :
    U * (1 : Matrix X X ℂ).submatrix id j = U.submatrix id j := by
  ext x a
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- Conjugating by the embedding `ψ ↦ ψ ⊗ |r⟩` appends the ancilla state `|r⟩⟨r|`. -/
theorem conj_submatrix_one_mk [Fintype A] [DecidableEq A] [DecidableEq R] (r : R)
    (ρ : Matrix A A ℂ) :
    conj ((1 : Matrix (A × R) (A × R) ℂ).submatrix id (·, r)) ρ = ρ ⊗ₖ single r r 1 := by
  ext ⟨a, s⟩ ⟨a', s'⟩
  rcases eq_or_ne s r with rfl | hs
  · rcases eq_or_ne s' s with rfl | hs'
    · simp [Matrix.mul_apply, Matrix.one_apply]
    · simp [Matrix.mul_apply, Matrix.one_apply, hs'.symm]
  · simp [Matrix.mul_apply, Matrix.one_apply, hs, hs.symm]

/-! ## Unitary dilations -/

/-- Kraus operators `K i : Matrix B A ℂ` with `∑ i, (K i)ᴴ * K i = 1` are the partial trace of a
unitary conjugation: for any injective `j : A → B × ι` there is a unitary `U` on `B × ι` with
`∑ i, K i ρ (K i)ᴴ = tr_ι (U (P ρ Pᴴ) Uᴴ)`, where `P` is the basis embedding of `j`. -/
theorem exists_unitary_sum_conj_eq [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype ι] [DecidableEq ι] {K : ι → Matrix B A ℂ} (hK : ∑ i, (K i)ᴴ * K i = 1)
    {j : A → B × ι} (hj : Function.Injective j) :
    ∃ U ∈ unitaryGroup (B × ι) ℂ, ∑ i, conj (K i) =
      traceRight B ι ∘ₗ conj U ∘ₗ conj ((1 : Matrix (B × ι) (B × ι) ℂ).submatrix id j) := by
  have hS : (stinespring K)ᴴ * stinespring K = 1 := by
    rw [conjTranspose_stinespring_mul_stinespring, hK]
  obtain ⟨U, hU, hUS⟩ := exists_unitary_submatrix_eq hS hj
  refine ⟨U, hU, ?_⟩
  rw [← conj_mul, mul_submatrix_one_id, hUS, sum_conj_eq_traceRight_comp_conj]

/-- **Unitary Stinespring dilation of a channel.** A completely positive trace-preserving map
`Φ : M_A → M_B` is `ρ ↦ tr_E (U (P ρ Pᴴ) Uᴴ)` with environment `E = B × A`, `U` unitary on
`B × E`, and `P` the basis embedding of any injective `j : A → B × E`. -/
theorem IsCP.exists_unitary_of_isTP [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {Φ : MatrixMap A B} (hΦ : Φ.IsCP) (htp : Φ.IsTP) {j : A → B × (B × A)}
    (hj : Function.Injective j) :
    ∃ U ∈ unitaryGroup (B × (B × A)) ℂ, Φ = traceRight B (B × A) ∘ₗ conj U ∘ₗ
      conj ((1 : Matrix (B × (B × A)) (B × (B × A)) ℂ).submatrix id j) := by
  obtain ⟨K, rfl, hK⟩ := hΦ.exists_kraus_of_isTP htp
  exact exists_unitary_sum_conj_eq hK hj

/-- **Unitary Stinespring dilation with an ancilla.** A completely positive trace-preserving map
`Φ : M_A → M_A` is `ρ ↦ tr_E (U (ρ ⊗ |r⟩⟨r|) Uᴴ)` with ancilla `E = A × A` prepared in any basis
state `r`, and `U` unitary on `A × E`. -/
theorem IsCP.exists_unitary_kronecker_of_isTP [Fintype A] [DecidableEq A] {Φ : MatrixMap A A}
    (hΦ : Φ.IsCP) (htp : Φ.IsTP) (r : A × A) :
    ∃ U ∈ unitaryGroup (A × (A × A)) ℂ,
      ∀ ρ, Φ ρ = traceRight A (A × A) (U * (ρ ⊗ₖ single r r 1) * Uᴴ) := by
  obtain ⟨U, hU, hΦU⟩ := hΦ.exists_unitary_of_isTP htp (Prod.mk_left_injective r)
  refine ⟨U, hU, fun ρ ↦ ?_⟩
  rw [hΦU, LinearMap.comp_apply, LinearMap.comp_apply, conj_submatrix_one_mk, conj_apply]

end MatrixMap

end Quantum

/-! ## Purification -/

namespace Matrix.PosSemidef

open Quantum.MatrixMap
open scoped MatrixOrder

variable {A : Type*} [Fintype A]

/-- **Purification.** A positive semidefinite `ρ` on `A` is the partial trace over the right
factor of `|ψ⟩⟨ψ|` for a vector `ψ` on `A × A`, with `⟨ψ, ψ⟩ = tr ρ`. A density matrix thus
has a unit-vector purification. -/
theorem exists_purification {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ∃ ψ : A × A → ℂ, star ψ ⬝ᵥ ψ = ρ.trace ∧
      ρ = Quantum.MatrixMap.traceRight A A (vecMulVec ψ (star ψ)) := by
  classical
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  let ψ : A × A → ℂ := fun x ↦ star (Y x.2 x.1)
  have hψ : ρ = Quantum.MatrixMap.traceRight A A (vecMulVec ψ (star ψ)) := by
    rw [hY]
    ext a a'
    simp [ψ, Matrix.mul_apply, vecMulVec_apply, star_eq_conjTranspose]
  refine ⟨ψ, ?_, hψ⟩
  rw [hψ, trace_traceRight, trace_vecMulVec, dotProduct_comm]

end Matrix.PosSemidef
