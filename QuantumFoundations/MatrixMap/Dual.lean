/-
Copyright (c) 2026 Bas Spitters, Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters, Quang Dao
-/

module

public import QuantumFoundations.MatrixMap.Kraus

/-!
# The trace dual of a matrix map

The trace dual of `Φ : M_A → M_B` is the map `dual Φ : M_B → M_A` with

`tr (dual Φ Y * X) = tr (Y * Φ X)`

for all `X : M_A` and `Y : M_B` (`trace_dual_mul`). The pairing `(Y, X) ↦ tr (Y * X)` is
complex-bilinear, so `dual Φ` is the transpose of `Φ` for this pairing. On maps that commute with
`conjTranspose`, such as completely positive maps, it is also the Hilbert–Schmidt adjoint: the
Heisenberg-picture map, which sends an observable on the output to an observable on the input.
For a Kraus map, `dual (conj K) = conj Kᴴ` (`dual_conj`).

The dual is a contravariant involution (`dual_id`, `dual_comp`, `dual_dual`). It turns trace
conditions into conditions on the image of the identity: `Φ` is trace preserving iff
`dual Φ 1 = 1` (`isTP_iff_dual_one`), and a completely positive `Φ` is trace nonincreasing iff
`dual Φ 1 ≤ 1` (`IsCP.isTNI_iff_dual_one`). The dual of a completely positive map is completely
positive (`IsCP.dual`).

## Main definitions

* `Quantum.MatrixMap.dual Φ`: the trace dual, with entry `tr (Y * Φ (single a' a 1))` at `(a, a')`.

## Main results

* `Quantum.MatrixMap.trace_dual_mul`: the defining identity `tr (dual Φ Y * X) = tr (Y * Φ X)`.
* `Quantum.MatrixMap.dual_id`, `Quantum.MatrixMap.dual_comp`, `Quantum.MatrixMap.dual_dual`.
* `Quantum.MatrixMap.dual_conj`, `Quantum.MatrixMap.dual_sum_conj_one`.
* `Quantum.MatrixMap.isTP_iff_dual_one`, `Quantum.MatrixMap.IsCP.isTNI_iff_dual_one`.
* `Quantum.MatrixMap.IsCP.dual`.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018, §2.2
  (adjoint maps).
-/

public section

open scoped ComplexOrder
open Matrix

namespace Quantum

namespace MatrixMap

variable {A B C ι : Type*}

section Dual

variable [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- The trace dual of `Φ : M_A → M_B`: the map `M_B → M_A` with
`tr (dual Φ Y * X) = tr (Y * Φ X)` (`trace_dual_mul`). Its entry at `(a, a')` is
`tr (Y * Φ (single a' a 1))`. -/
@[expose]
def dual (Φ : MatrixMap A B) : MatrixMap B A where
  toFun Y := Matrix.of fun a a' ↦ (Y * Φ (single a' a 1)).trace
  map_add' Y Z := by
    ext a a'
    simp [Matrix.add_mul]
  map_smul' c Y := by
    ext a a'
    simp

/-- The entry of `dual Φ Y` at `(a, a')` is `tr (Y * Φ (single a' a 1))`. -/
@[simp]
theorem dual_apply (Φ : MatrixMap A B) (Y : Matrix B B ℂ) (a a' : A) :
    dual Φ Y a a' = (Y * Φ (single a' a 1)).trace :=
  rfl

/-- The defining identity of the trace dual: `tr (dual Φ Y * X) = tr (Y * Φ X)`. -/
theorem trace_dual_mul [Fintype A] (Φ : MatrixMap A B) (Y : Matrix B B ℂ) (X : Matrix A A ℂ) :
    (dual Φ Y * X).trace = (Y * Φ X).trace := by
  have hX : X = ∑ a, ∑ a', X a a' • single a a' (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp_rw [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_rhs => rw [hX]
  simp only [map_sum, map_smul, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply (M := dual Φ Y), dual_apply]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- The trace dual is the only map satisfying the defining identity. -/
theorem eq_dual_iff [Fintype A] {Φ : MatrixMap A B} {Ψ : MatrixMap B A} :
    Ψ = dual Φ ↔ ∀ Y X, (Ψ Y * X).trace = (Y * Φ X).trace := by
  refine ⟨fun h ↦ h ▸ trace_dual_mul Φ, fun h ↦ LinearMap.ext fun Y ↦ ?_⟩
  exact Matrix.ext_iff_trace_mul_right.mpr fun X ↦ by rw [h, trace_dual_mul]

/-- The trace dual of the identity is the identity. -/
@[simp]
theorem dual_id [Fintype A] : dual (LinearMap.id : MatrixMap A A) = LinearMap.id :=
  (eq_dual_iff.mpr fun _ _ ↦ rfl).symm

/-- The trace dual of the zero map is zero. -/
@[simp]
theorem dual_zero : dual (0 : MatrixMap A B) = 0 := by
  ext Y a a'
  simp

/-- The trace dual is additive. -/
theorem dual_add (Φ Ψ : MatrixMap A B) : dual (Φ + Ψ) = dual Φ + dual Ψ := by
  ext Y a a'
  simp [Matrix.mul_add]

/-- The trace dual commutes with scalar multiplication. -/
theorem dual_smul (c : ℂ) (Φ : MatrixMap A B) : dual (c • Φ) = c • dual Φ := by
  ext Y a a'
  simp

/-- The trace dual commutes with finite sums. -/
theorem dual_sum (s : Finset ι) (Φ : ι → MatrixMap A B) :
    dual (∑ i ∈ s, Φ i) = ∑ i ∈ s, dual (Φ i) := by
  ext Y a a'
  simp [LinearMap.sum_apply, Matrix.mul_sum, Matrix.sum_apply]

/-- The trace dual reverses composition: `dual (Ψ ∘ Φ) = dual Φ ∘ dual Ψ`. -/
theorem dual_comp [Finite A] (Ψ : MatrixMap B C) (Φ : MatrixMap A B) :
    dual (Ψ ∘ₗ Φ) = dual Φ ∘ₗ dual Ψ := by
  cases nonempty_fintype A
  exact (eq_dual_iff.mpr fun Z X ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, trace_dual_mul, trace_dual_mul]).symm

/-- The trace dual is an involution. -/
@[simp]
theorem dual_dual [Fintype A] (Φ : MatrixMap A B) : dual (dual Φ) = Φ :=
  ((eq_dual_iff (Φ := dual Φ)).mpr fun X Y ↦ by
    rw [Matrix.trace_mul_comm, ← trace_dual_mul, Matrix.trace_mul_comm]).symm

/-- The trace dual of the Kraus map of `K` is the Kraus map of `Kᴴ`. -/
theorem dual_conj [Fintype A] (K : Matrix B A ℂ) : dual (conj K) = conj Kᴴ :=
  (eq_dual_iff.mpr fun Y X ↦ by
    simp only [conj_apply, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Kᴴ]
    simp only [Matrix.mul_assoc]).symm

/-- The trace dual of a sum of Kraus maps sends the identity to `∑ i, (K i)ᴴ * K i`. -/
theorem dual_sum_conj_one [Fintype A] [Fintype ι] (K : ι → Matrix B A ℂ) :
    dual (∑ i, conj (K i)) 1 = ∑ i, (K i)ᴴ * K i := by
  simp [dual_sum, dual_conj, LinearMap.sum_apply]

/-- A map is trace preserving iff its trace dual is unital. -/
theorem isTP_iff_dual_one [Fintype A] {Φ : MatrixMap A B} : Φ.IsTP ↔ dual Φ 1 = 1 := by
  rw [Matrix.ext_iff_trace_mul_right]
  refine forall_congr' fun X ↦ ?_
  rw [trace_dual_mul, Matrix.one_mul, Matrix.one_mul]

/-- A completely positive map is trace nonincreasing iff its trace dual sends the identity to a
contraction, `dual Φ 1 ≤ 1`, expressed as positive semidefiniteness of `1 - dual Φ 1`. -/
theorem IsCP.isTNI_iff_dual_one [Fintype A] {Φ : MatrixMap A B} (hΦ : Φ.IsCP) :
    Φ.IsTNI ↔ (1 - dual Φ 1).PosSemidef := by
  obtain ⟨K, rfl⟩ := hΦ.exists_kraus
  rw [dual_sum_conj_one, isTNI_sum_conj_iff]

/-- The trace dual of a completely positive map is completely positive. -/
theorem IsCP.dual [Finite A] {Φ : MatrixMap A B} (hΦ : Φ.IsCP) :
    (MatrixMap.dual Φ).IsCP := by
  cases nonempty_fintype A
  obtain ⟨K, rfl⟩ := hΦ.exists_kraus
  rw [dual_sum]
  simp_rw [dual_conj]
  exact isCP_sum_conj _

end Dual

end MatrixMap

end Quantum
