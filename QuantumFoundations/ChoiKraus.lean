/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import Mathlib.Analysis.Matrix.Order
public import QuantumFoundations.CPMap

/-!
# Choi matrix and Kraus representation of completely positive maps

For a linear map `Φ` on complex matrices `Matrix n n ℂ` over a finite type `n`,
the Choi matrix is the `(n × n) × (n × n)` matrix whose `(a, b)` block is
`Φ (matUnit a b)`. It is the image of the unnormalised maximally entangled
projector under `id_n ⊗ Φ`, so complete positivity in the sense of `IsCPMap` makes
it positive semidefinite. A factorisation `choi Φ = Bᴴ * B` (through the matrix
square root) yields `|n|·|n|` Kraus operators.

## Main definitions

* `choi` — the Choi matrix of `Φ`, indexed by `n × n`.
* `krausOfFactor` — the Kraus operators read off a factor `B` of the Choi matrix.

## Main results

* `choi_posSemidef` — `IsCPMap Φ → (choi Φ).PosSemidef`.
* `exists_kraus_of_choi_posSemidef`, `exists_kraus` — a map with PSD Choi matrix,
  in particular a CP map, is a Kraus sum over `n × n`.
* `exists_kraus_fin` — the same with index set `Fin (|n| * |n|)`;
  `exists_kraus_fin_fin` is its form at `n = Fin d` with index set `Fin (d * d)`.
* `kraus_sum_conjTranspose_mul_self_eq_one` — the Kraus operators of a
  trace-preserving map satisfy `∑ i, (K i)ᴴ * K i = 1`.
* `isCPMap_of_kraus` — a Kraus sum is completely positive.
* `isCPMap_iff_exists_kraus`, `isCPMap_iff_choi_posSemidef` — the two
  characterisations of complete positivity.

## References

* M.-D. Choi, *Completely positive linear maps on complex matrices*, Linear Algebra
  Appl. 10 (1975)
* Watrous, *The Theory of Quantum Information* (Cambridge, 2018), §2.2
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

namespace Quantum

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The Choi matrix -/

/-- The Choi matrix of `Φ`: `choi Φ (a, i) (b, j) = Φ (matUnit a b) i j`. -/
def choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ :=
  fun p q => Φ (matUnit p.1 q.1) p.2 q.2

/-- Entry formula of the Choi matrix. -/
theorem choi_apply (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (a i b j : n) : choi Φ (a, i) (b, j) = Φ (matUnit a b) i j := rfl

/-- The unnormalised maximally entangled vector `∑ a, e_a ⊗ e_a`. -/
def maxEntVec : n × n → ℂ := fun p => if p.1 = p.2 then 1 else 0

/-- The `(a, b)` block of `|Ω⟩⟨Ω|` is the matrix unit `matUnit a b`. -/
theorem blockMatrix_maxEnt (a b : n) :
    blockMatrix (vecMulVec (maxEntVec (n := n)) (star maxEntVec)) a b = matUnit a b := by
  ext i j
  simp only [blockMatrix, vecMulVec_apply, Pi.star_apply, maxEntVec, matUnit_apply]
  by_cases hai : a = i <;> by_cases hbj : b = j <;> simp [hai, hbj, eq_comm]

/-- The Choi matrix is `(id_k ⊗ Φ) |Ω⟩⟨Ω|`, with the first factor of `n × n`
relabelled along an equivalence `e : n ≃ Fin k`. -/
theorem choi_eq_tensorIdMap {k : ℕ} (e : n ≃ Fin k)
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    choi Φ = (tensorIdMap Φ k ((vecMulVec maxEntVec (star maxEntVec)).submatrix
      (Prod.map e.symm id) (Prod.map e.symm id))).submatrix (Prod.map e id) (Prod.map e id) := by
  funext p q
  rw [submatrix_apply, tensorIdMap_apply]
  have hblock : blockMatrix ((vecMulVec maxEntVec (star maxEntVec)).submatrix
      (Prod.map e.symm id) (Prod.map e.symm id)) (Prod.map e id p).1 (Prod.map e id q).1 =
      blockMatrix (vecMulVec (maxEntVec (n := n)) (star maxEntVec)) p.1 q.1 := by
    ext i j
    simp [blockMatrix]
  rw [hblock, blockMatrix_maxEnt]
  rfl

/-- The Choi matrix of a completely positive map is positive semidefinite. -/
theorem choi_posSemidef {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΦ : IsCPMap Φ) : (choi Φ).PosSemidef := by
  rw [choi_eq_tensorIdMap (Fintype.equivFin n)]
  exact (hΦ _ _ ((posSemidef_vecMulVec_self_star _).submatrix _)).submatrix _

/-! ## Kraus operators from a factorisation of the Choi matrix -/

/-- The Kraus operators read off a factor `B` of the Choi matrix:
`krausOfFactor B r i a = star (B r (a, i))`. -/
def krausOfFactor {r : Type*} (B : Matrix r (n × n) ℂ) (x : r) :
    Matrix n n ℂ :=
  Matrix.of fun i a => star (B x (a, i))

/-- If `choi Φ = Bᴴ * B`, then `Φ` is the Kraus sum of `krausOfFactor B`. -/
theorem eq_kraus_of_choi_eq {r : Type*} [Fintype r]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (B : Matrix r (n × n) ℂ) (hB : choi Φ = Bᴴ * B)
    (ρ : Matrix n n ℂ) :
    Φ ρ = ∑ x, krausOfFactor B x * ρ * (krausOfFactor B x)ᴴ := by
  ext i j
  rw [linearMap_expand Φ ρ i j, Finset.sum_matrix_entry]
  have hc : ∀ a b, Φ (matUnit a b) i j = ∑ x, star (B x (a, i)) * B x (b, j) := by
    intro a b
    rw [← choi_apply, hB, mul_apply]
    rfl
  simp_rw [hc, mul_apply, conjTranspose_apply, krausOfFactor, of_apply, star_star,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => by ring

/-- A positive semidefinite complex matrix is `Bᴴ * B` for a square `B`. -/
theorem exists_eq_conjTranspose_mul_self_of_posSemidef {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, A = Bᴴ * B := by
  classical
  have h0 : 0 ≤ A := nonneg_iff_posSemidef.mpr hA
  refine ⟨CFC.sqrt A, ?_⟩
  have hs : star (CFC.sqrt A) = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
  rw [← star_eq_conjTranspose, hs, CFC.sqrt_mul_sqrt_self A h0]

/-- A map whose Choi matrix is positive semidefinite is a Kraus sum over
`n × n`. -/
theorem exists_kraus_of_choi_posSemidef
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΦ : (choi Φ).PosSemidef) :
    ∃ K : n × n → Matrix n n ℂ,
      ∀ ρ, Φ ρ = ∑ x, K x * ρ * (K x)ᴴ := by
  obtain ⟨B, hB⟩ := exists_eq_conjTranspose_mul_self_of_posSemidef hΦ
  exact ⟨krausOfFactor B, eq_kraus_of_choi_eq Φ B hB⟩

/-- Kraus representation: a completely positive map is a Kraus sum over
`n × n`. -/
theorem exists_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΦ : IsCPMap Φ) :
    ∃ K : n × n → Matrix n n ℂ,
      ∀ ρ, Φ ρ = ∑ x, K x * ρ * (K x)ᴴ :=
  exists_kraus_of_choi_posSemidef (choi_posSemidef hΦ)

/-- Kraus representation with `|n| * |n|` operators indexed by
`Fin (Fintype.card n * Fintype.card n)`. -/
theorem exists_kraus_fin {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΦ : IsCPMap Φ) :
    ∃ K : Fin (Fintype.card n * Fintype.card n) → Matrix n n ℂ,
      ∀ ρ, Φ ρ = ∑ i, K i * ρ * (K i)ᴴ := by
  obtain ⟨K, hK⟩ := exists_kraus hΦ
  let e : n × n ≃ Fin (Fintype.card n * Fintype.card n) :=
    Fintype.equivFinOfCardEq (Fintype.card_prod n n)
  refine ⟨fun i => K (e.symm i), fun ρ => ?_⟩
  rw [hK ρ]
  exact (e.symm.sum_comp (fun x => K x * ρ * (K x)ᴴ)).symm

/-- Kraus representation of a map on `Fin d`-indexed matrices with `d * d`
operators indexed by `Fin (d * d)`. -/
theorem exists_kraus_fin_fin {d : ℕ}
    {Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ} (hΦ : IsCPMap Φ) :
    ∃ K : Fin (d * d) → Matrix (Fin d) (Fin d) ℂ,
      ∀ ρ, Φ ρ = ∑ i, K i * ρ * (K i)ᴴ := by
  obtain ⟨K, hK⟩ := exists_kraus hΦ
  refine ⟨fun i => K (finProdFinEquiv.symm i), fun ρ => ?_⟩
  rw [hK ρ]
  exact (finProdFinEquiv.symm.sum_comp (fun x => K x * ρ * (K x)ᴴ)).symm

/-! ## Trace preservation -/

/-- The Kraus operators of a trace-preserving map satisfy the completeness
relation `∑ x, (K x)ᴴ * K x = 1`. -/
theorem kraus_sum_conjTranspose_mul_self_eq_one {r : Type*} [Fintype r]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    {K : r → Matrix n n ℂ} (hK : ∀ ρ, Φ ρ = ∑ x, K x * ρ * (K x)ᴴ)
    (hTP : IsTP Φ) : ∑ x, (K x)ᴴ * K x = 1 := by
  have htr : ∀ ρ, ((∑ x, (K x)ᴴ * K x) * ρ).trace = ρ.trace := by
    intro ρ
    rw [← hTP ρ, hK ρ, trace_sum, Finset.sum_mul, trace_sum]
    exact Finset.sum_congr rfl fun x _ => trace_mul_cycle (K x) ρ (K x)ᴴ |>.symm
  refine Matrix.ext fun i j => ?_
  rw [← trace_mul_matUnit (∑ x, (K x)ᴴ * K x) i j, htr,
    ← trace_mul_matUnit (1 : Matrix n n ℂ) i j, Matrix.one_mul]

/-! ## Kraus sums are completely positive -/

/-- A Kraus sum `ρ ↦ ∑ x, K x * ρ * (K x)ᴴ` is completely positive. -/
theorem isCPMap_of_kraus {r : Type*} [Fintype r]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (K : r → Matrix n n ℂ) (hK : ∀ ρ, Φ ρ = ∑ x, K x * ρ * (K x)ᴴ) :
    IsCPMap Φ := by
  classical
  let C : r → (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) := fun x =>
    (LinearMap.mulLeft ℂ (K x)).comp (LinearMap.mulRight ℂ (K x)ᴴ)
  have hC : ∀ x ρ, C x ρ = K x * ρ * (K x)ᴴ := fun x ρ => by
    simp [C, Matrix.mul_assoc]
  intro k M hM
  have hsum : tensorIdMap Φ k M = ∑ x, tensorIdMap (C x) k M := by
    funext p q
    rw [tensorIdMap_apply, hK, Finset.sum_matrix_entry, Finset.sum_matrix_entry]
    simp only [tensorIdMap_apply, hC]
  rw [hsum]
  exact posSemidef_sum _ fun x _ =>
    isCPMap_conj (K x) (C x) (hC x) k M hM

/-! ## Characterisations of complete positivity -/

/-- A linear map is completely positive iff it is a Kraus sum over `n × n`. -/
theorem isCPMap_iff_exists_kraus
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} :
    IsCPMap Φ ↔ ∃ K : n × n → Matrix n n ℂ,
      ∀ ρ, Φ ρ = ∑ x, K x * ρ * (K x)ᴴ :=
  ⟨exists_kraus, fun ⟨K, hK⟩ => isCPMap_of_kraus K hK⟩

/-- Choi's theorem: a linear map is completely positive iff its Choi matrix is
positive semidefinite. -/
theorem isCPMap_iff_choi_posSemidef
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} :
    IsCPMap Φ ↔ (choi Φ).PosSemidef :=
  ⟨choi_posSemidef, fun h =>
    let ⟨K, hK⟩ := exists_kraus_of_choi_posSemidef h
    isCPMap_of_kraus K hK⟩

end Quantum
