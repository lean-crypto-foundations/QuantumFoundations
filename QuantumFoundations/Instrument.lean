/-
Copyright (c) 2024 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Positive instruments and the `QComp` monad

This file defines the type `QComp d α` of families `{E_a}_{a ∈ α}` of linear maps
on complex matrices `Matrix d d ℂ` that are positive (each `E_a` maps positive
semidefinite matrices to positive semidefinite matrices), summable, and whose sum
is trace-non-increasing on positive semidefinite inputs; the missing trace is the
probability of abort. It defines the unit and Kleisli composition and proves that
`QComp d` is a lawful monad.

A quantum instrument in the physical sense also requires every branch to be
completely positive. `QComp` does not: it contains positive maps that are not
completely positive, such as the one-outcome transpose map `ρ ↦ ρᵀ`, which does not
describe a physical operation on half of an entangled state. The unit, Kleisli
composition, monad laws and the results of this file need only positivity. Results
that need complete positivity, such as the local lifts `TensorProduct.localOp₁`,
`TensorProduct.localOp₂` and `QComp.tensor`, take it as a hypothesis on the branches.

## Main definitions

* `Quantum.DensityMatrix`: a positive semidefinite matrix of trace one.
* `Quantum.QComp`: a summable family of positive maps with outcomes in `α` whose sum
  is trace-non-increasing; complete positivity is not required.
* `Quantum.QComp.qpure`, `Quantum.QComp.qbind`: the unit and the Kleisli
  composition of instruments.
* `Quantum.QComp.qfail`: the instrument that aborts with probability one.
* `Quantum.prTrue_Q`: the probability of outcome `true` of a Boolean instrument.

## Main results

* `Quantum.psd_norm_le_trace`: the entrywise sup-norm of a positive
  semidefinite matrix is at most its trace.
* `Quantum.tsum_posSemidef`, `Quantum.trace_tsum`: sums of positive
  semidefinite matrices and their traces.
* `Quantum.QComp.qpure_qbind`, `Quantum.QComp.qbind_qpure`,
  `Quantum.QComp.qbind_assoc`: the monad laws, packaged as `LawfulMonad (QComp d)`.
* `Quantum.absDiff_prTrue_Q_qbind_le`: composing a shared instrument with two
  continuations whose acceptance probabilities differ by at most `ε` on every
  state yields acceptance probabilities that differ by at most `ε`.

## Implementation notes

The summability of `qbind` rests on a uniform bound `‖L M‖ ≤ 2n(2n+1) ‖M‖`,
where `n = Fintype.card d`,
for every positivity-preserving trace-non-increasing linear map `L`, and on
the same bound for the sum of the norms of the branches of an instrument. A
Hermitian `H` is shifted to the positive semidefinite `H + n‖H‖ • 1`; a
general `M` is written `H₁ + (-i) • H₂` with Hermitian `H₁`, `H₂`.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press,
  2018, Chapter 2.
-/

@[expose] public section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.Elementwise
open Matrix

noncomputable section

namespace Quantum

variable {d : Type*} [Fintype d] {α β γ δ : Type}

/-! ## Helper: trace of PSD is non-negative -/

/-- The trace of a positive semidefinite matrix has nonnegative real part. -/
theorem trace_re_nonneg_of_psd {ρ : Matrix d d ℂ}
    (hρ : ρ.PosSemidef) : 0 ≤ ρ.trace.re :=
  (Complex.nonneg_iff.mp hρ.trace_nonneg).1

/-! ## Density Matrices -/

/-- A density matrix on a system with basis indexed by `d`: a positive semidefinite
complex matrix of trace one. -/
structure DensityMatrix (d : Type*) [Fintype d] where
  /-- The underlying matrix. -/
  val : Matrix d d ℂ
  /-- The matrix is positive semidefinite. -/
  psd : val.PosSemidef
  /-- The matrix has trace one. -/
  tr_one : val.trace = 1

/-! ## QComp Definition -/

/-- A positive instrument on a system with basis indexed by a finite type `d` with outcomes
in `α`: a summable family of positive linear maps on complex matrices `Matrix d d ℂ` whose sum is
trace-non-increasing on positive semidefinite inputs. The branches need not be
completely positive (the transpose map is a one-outcome `QComp`), so a `QComp` is
a quantum instrument in the physical sense only when every branch satisfies
`IsCPMap`; results that need this take it as a hypothesis. -/
structure QComp (d : Type*) [Fintype d] (α : Type) where
  /-- The linear map applied on outcome `a`. -/
  branch : α → (Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
  /-- Each branch maps positive semidefinite matrices to positive semidefinite
  matrices. -/
  branch_psd : ∀ a (ρ : Matrix d d ℂ), ρ.PosSemidef →
    (branch a ρ).PosSemidef
  /-- The branches applied to a fixed matrix form a summable family. -/
  branch_summable : ∀ (ρ : Matrix d d ℂ),
    Summable (fun a => branch a ρ)
  /-- The total trace of the branches is at most the trace of the input. -/
  branch_stp : ∀ (ρ : Matrix d d ℂ), ρ.PosSemidef →
    (∑' a, (branch a ρ).trace).re ≤ ρ.trace.re

/-! ## Extensional Equality -/

/-- Two instruments with equal branches are equal. -/
@[ext]
theorem QComp.ext {I J : QComp d α}
    (h : ∀ a, I.branch a = J.branch a) : I = J := by
  cases I; cases J; congr 1; funext a; exact h a

/-- Two instruments whose branches agree on every matrix are equal. -/
theorem QComp.ext_fun {I J : QComp d α}
    (h : ∀ a (ρ : Matrix d d ℂ), I.branch a ρ = J.branch a ρ) :
    I = J :=
  QComp.ext (fun a => LinearMap.ext (h a))

/-! ## Pure -/

open Classical in
/-- The deterministic instrument with outcome `a`: its branch at `a` is the
identity and every other branch is zero. -/
def QComp.qpure (a : α) : QComp d α where
  branch a' := if a' = a then LinearMap.id else 0
  branch_psd a' ρ hρ := by
    split_ifs with h <;> simp_all [Matrix.PosSemidef.zero]
  branch_summable ρ := by
    suffices h : Summable (fun a' => if a' = a then ρ else (0 : Matrix d d ℂ)) by
      refine h.congr ?_
      intro a'
      split_ifs <;> simp
    apply summable_of_ne_finset_zero (s := {a})
    intro b hb
    simp only [Finset.mem_singleton] at hb
    simp [hb]
  branch_stp ρ _ := by
    have heq : (fun a' => ((if a' = a then
        (LinearMap.id : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
        else 0) ρ).trace) =
        (fun a' => if a' = a then ρ.trace else 0) := by
      funext a'; split_ifs <;> simp
    simp only [heq, tsum_ite_eq a (fun _ => ρ.trace)]
    exact le_refl _

/-! ## Fail -/

/-- The instrument whose branches are all zero: it aborts with probability one. -/
def QComp.qfail : QComp d α where
  branch _ := 0
  branch_psd _ _ _ := Matrix.PosSemidef.zero
  branch_summable _ := summable_zero
  branch_stp ρ hρ := by
    change (∑' (_ : α), (0 : Matrix d d ℂ).trace).re ≤ ρ.trace.re
    simp only [Matrix.trace_zero, tsum_zero, Complex.zero_re]
    exact trace_re_nonneg_of_psd hρ

/-! ## Summability Infrastructure for PSD Matrices -/

omit [Fintype d] in
/-- Cauchy–Schwarz for PSD matrices: `|M i j|² ≤ (M i i).re * (M j j).re`.
    Proved via non-negative determinant of the 2×2 principal submatrix. -/
theorem psd_cauchy_schwarz {M : Matrix d d ℂ} (hM : M.PosSemidef)
    (i j : d) : Complex.normSq (M i j) ≤ (M i i).re * (M j j).re := by
  have hN : (M.submatrix (![i, j]) (![i, j])).PosSemidef := hM.submatrix _
  have hdet_nn : 0 ≤ (M.submatrix (![i, j]) (![i, j])).det := hN.det_nonneg
  have hdet_eq : (M.submatrix (![i, j]) (![i, j])).det =
      M i i * M j j - M i j * M j i := by
    rw [Matrix.det_fin_two]
    simp [Matrix.submatrix_apply]
  have hconj : M j i = starRingEnd ℂ (M i j) := by
    have := congr_fun (congr_fun hM.isHermitian j) i
    simp [conjTranspose_apply] at this; exact this.symm
  have hii_im : (M i i).im = 0 :=
    Complex.conj_eq_iff_im.mp (congr_fun (congr_fun hM.isHermitian i) i)
  have hjj_im : (M j j).im = 0 :=
    Complex.conj_eq_iff_im.mp (congr_fun (congr_fun hM.isHermitian j) j)
  rw [hdet_eq, hconj, Complex.mul_conj] at hdet_nn
  have hre := (Complex.nonneg_iff.mp hdet_nn).1
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hprod_re : (M i i * M j j).re = (M i i).re * (M j j).re := by
    simp [Complex.mul_re, hii_im, hjj_im]
  linarith

/-- Entry norm bound for PSD matrices: `‖M i j‖ ≤ trace(M).re`. -/
theorem psd_entry_norm_le_trace {M : Matrix d d ℂ} (hM : M.PosSemidef)
    (i j : d) : ‖M i j‖ ≤ M.trace.re := by
  have hdiag_nn : ∀ k, 0 ≤ (M k k).re :=
    fun k => (Complex.nonneg_iff.mp (hM.diag_nonneg)).1
  have htrace_re : M.trace.re = ∑ k : d, (M k k).re := by
    simp [Matrix.trace]
  have htrace_nn : 0 ≤ M.trace.re := trace_re_nonneg_of_psd hM
  have hcs := psd_cauchy_schwarz hM i j
  have hai : (M i i).re ≤ M.trace.re := by
    rw [htrace_re]; exact Finset.single_le_sum (fun k _ => hdiag_nn k) (Finset.mem_univ i)
  have haj : (M j j).re ≤ M.trace.re := by
    rw [htrace_re]; exact Finset.single_le_sum (fun k _ => hdiag_nn k) (Finset.mem_univ j)
  have hab_le : (M i i).re * (M j j).re ≤ M.trace.re ^ 2 := by
    calc (M i i).re * (M j j).re ≤ M.trace.re * M.trace.re :=
          mul_le_mul hai haj (hdiag_nn j) htrace_nn
      _ = M.trace.re ^ 2 := (sq M.trace.re).symm
  have h_sq_le : ‖M i j‖ ^ 2 ≤ M.trace.re ^ 2 := by
    calc ‖M i j‖ ^ 2 = Complex.normSq (M i j) := Complex.sq_norm (M i j)
      _ ≤ (M i i).re * (M j j).re := hcs
      _ ≤ M.trace.re ^ 2 := hab_le
  nlinarith [norm_nonneg (M i j), sq_nonneg (M.trace.re - ‖M i j‖)]

/-- For PSD matrices, the sup-norm is bounded by the trace.
    Uses `psd_cauchy_schwarz` (2×2 principal minor determinant) and `Matrix.norm_le_iff`. -/
theorem psd_norm_le_trace {M : Matrix d d ℂ} (hM : M.PosSemidef) :
    ‖M‖ ≤ M.trace.re :=
  (Matrix.norm_le_iff (trace_re_nonneg_of_psd hM)).mpr (psd_entry_norm_le_trace hM)

/-- A family of PSD matrices with summable traces is summable (in the product/norm topology). -/
theorem psd_summable_of_trace_summable {f : α → Matrix d d ℂ}
    (hpsd : ∀ a, (f a).PosSemidef)
    (htrace : Summable (fun a => (f a).trace.re)) :
    Summable f :=
  summable_norm_iff.mp
    (htrace.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => psd_norm_le_trace (hpsd a)))

omit [Fintype d] in
/-- Entry-wise summability from matrix summability. -/
private theorem summable_entry {f : α → Matrix d d ℂ}
    (hf : Summable f) (i j : d) : Summable (fun a => f a i j) :=
  Pi.summable.mp (Pi.summable.mp hf i) j

omit [Fintype d] in
/-- Entry-wise tsum for summable matrix families. -/
private theorem tsum_entry {f : α → Matrix d d ℂ}
    (hf : Summable f) (i j : d) :
    (∑' a, f a) i j = ∑' a, f a i j := by
  have h1 : (∑' a, f a) i = ∑' a, f a i := Pi.tsum_apply hf
  have h2 : (∑' a, f a i) j = ∑' a, f a i j := Pi.tsum_apply (Pi.summable.mp hf i)
  exact (congr_fun h1 j).trans h2

omit [Fintype d] in
/-- Tsum of Hermitian matrices is Hermitian. -/
private theorem tsum_isHermitian {f : α → Matrix d d ℂ}
    (hH : ∀ a, (f a).IsHermitian) (hf : Summable f) :
    (∑' a, f a).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply]
  rw [tsum_entry hf j i, tsum_entry hf i j, tsum_star]
  congr 1; ext a
  exact congr_fun (congr_fun (hH a) i) j

omit [Fintype d] in
/-- Tsum of PSD matrices is PSD (summable family). -/
theorem tsum_posSemidef [Finite d] {f : α → Matrix d d ℂ}
    (hpsd : ∀ a, (f a).PosSemidef) (hf : Summable f) :
    (∑' a, f a).PosSemidef := by
  have := Fintype.ofFinite d
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨tsum_isHermitian (fun a => (hpsd a).isHermitian) hf, fun x => ?_⟩
  -- Show: star x ⬝ᵥ (∑' a, f a) *ᵥ x = ∑' a, star x ⬝ᵥ f a *ᵥ x, then use tsum_nonneg
  suffices h : star x ⬝ᵥ (∑' a, f a) *ᵥ x = ∑' a, star x ⬝ᵥ f a *ᵥ x by
    rw [h]; exact tsum_nonneg (fun a => (posSemidef_iff_dotProduct_mulVec.mp (hpsd a)).2 x)
  -- Push the quadratic form through the tsum using finite-sum/tsum interchange
  have hentry : ∀ i j, Summable (fun a => f a i j) := summable_entry hf
  have hentry_mul : ∀ i j, Summable (fun a => f a i j * x j) :=
    fun i j => (hentry i j).mul_right _
  have hrow : ∀ i, Summable (fun a => ∑ j : d, f a i j * x j) :=
    fun i => summable_sum fun j _ => hentry_mul i j
  simp only [dotProduct, mulVec]
  simp_rw [tsum_entry hf]
  simp_rw [← tsum_mul_right]
  simp_rw [show ∀ i, ∑ j : d, ∑' a, f a i j * x j =
      ∑' a, ∑ j : d, f a i j * x j from fun i => by
    rw [show (∑ j : d, ∑' a, f a i j * x j) =
        (∑ j ∈ Finset.univ, ∑' a, (fun j' a' => f a' i j' * x j') j a) from by simp]
    rw [← Summable.tsum_finsetSum (fun j _ => hentry_mul i j)]]
  simp_rw [← tsum_mul_left]
  rw [show (∑ i : d, ∑' a, star x i * ∑ j : d, f a i j * x j) =
      (∑ i ∈ Finset.univ, ∑' a,
        (fun i' a' => star x i' * ∑ j : d, f a' i' j * x j) i a) from by simp]
  rw [← Summable.tsum_finsetSum (fun i _ => (hrow i).mul_left _)]

/-- Trace commutes with tsum for summable matrix families. -/
theorem trace_tsum {f : α → Matrix d d ℂ} (hf : Summable f) :
    (∑' a, f a).trace = ∑' a, (f a).trace := by
  simp [Matrix.trace, tsum_entry hf, Summable.tsum_finsetSum fun j _ => summable_entry hf j j]

/-- The trace, as a ContinuousLinearMap from matrices to ℂ. -/
def traceCLM (d : Type*) [Fintype d] : Matrix d d ℂ →L[ℂ] ℂ :=
  (traceLinearMap d ℂ ℂ).toContinuousLinearMap

/-- Summability of traces from summability of matrices. -/
theorem trace_summable {f : α → Matrix d d ℂ} (hf : Summable f) :
    Summable (fun a => (f a).trace) :=
  (traceCLM d).summable hf

/-- Summability of trace real parts from summability of matrices. -/
theorem trace_re_summable {f : α → Matrix d d ℂ} (hf : Summable f) :
    Summable (fun a => (f a).trace.re) :=
  (trace_summable hf).map Complex.reAddGroupHom Complex.continuous_re

/-! ## Operator Norm Bounds for Instruments

Proved bounds for positive sub-trace-preserving (sub-TP) maps:

* `single_stp_re`: A single branch of a sub-TP instrument has trace ≤ input trace.
* `subTP_opNorm_le`: `‖L(M)‖ ≤ 2d(2d+1) · ‖M‖` for a single branch.
* `instrument_l1_le`: `∑ᵦ ‖Lᵦ(M)‖ ≤ 2d(2d+1) · ‖M‖` for all branches combined.

**Proof structure** (Hermitian shift decomposition):
For PSD input M: L(M) is PSD with trace ≤ trace(M), so ‖L(M)‖ ≤ trace(M) ≤ d·‖M‖.
For Hermitian H: shift H + d‖H‖·I to make PSD, use triangle inequality → d(2d+1)·‖H‖.
For general M: decompose M = H₁ + (-i)H₂ with ‖Hₖ‖ ≤ ‖M‖ → 2d(2d+1)·‖M‖.
-/

/-- Single branch sub-TP: trace of one branch ≤ trace of input, for PSD input. -/
private lemma single_stp_re
    {α : Type}
    (branch : α → (Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ))
    (hpsd : ∀ a (ρ : Matrix d d ℂ), ρ.PosSemidef → (branch a ρ).PosSemidef)
    (hsum : ∀ (ρ : Matrix d d ℂ), Summable (fun a => branch a ρ))
    (hstp : ∀ (ρ : Matrix d d ℂ), ρ.PosSemidef →
      (∑' a, (branch a ρ).trace).re ≤ ρ.trace.re)
    (b : α) (M : Matrix d d ℂ) (hM : M.PosSemidef) :
    (branch b M).trace.re ≤ M.trace.re := by
  calc (branch b M).trace.re
      ≤ ∑' a, (branch a M).trace.re :=
        (trace_re_summable (hsum M)).le_tsum b
          (fun j _ => trace_re_nonneg_of_psd (hpsd j M hM))
    _ = (∑' a, (branch a M).trace).re :=
        (Complex.re_tsum (trace_summable (hsum M))).symm
    _ ≤ M.trace.re := hstp M hM

private lemma QComp.single_stp (I : QComp d α) (b : α)
    (M : Matrix d d ℂ) (hM : M.PosSemidef) :
    (I.branch b M).trace.re ≤ M.trace.re :=
  single_stp_re I.branch I.branch_psd I.branch_summable I.branch_stp b M hM

/-- For PSD-preserving sub-TP map L and PSD input M, ‖L(M)‖ ≤ trace(M).re.
    Proof: L(M) is PSD, so ‖L(M)‖ ≤ trace(L(M)).re ≤ trace(M).re. -/
private theorem subTP_psd_norm_le
    {d : Type*} [Fintype d]
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hpsd : ∀ (M : Matrix d d ℂ), M.PosSemidef → (L M).PosSemidef)
    (hstp : ∀ (M : Matrix d d ℂ), M.PosSemidef → (L M).trace.re ≤ M.trace.re)
    (M : Matrix d d ℂ) (hM : M.PosSemidef) :
    ‖L M‖ ≤ M.trace.re :=
  le_trans (psd_norm_le_trace (hpsd M hM)) (hstp M hM)

/-- Quadratic form bound via Cauchy-Schwarz: `|⟨x, Mx⟩| ≤ d · ‖M‖ · ‖x‖²`. -/
private lemma norm_quadratic_form_le {d : Type*} [Fintype d]
    (M : Matrix d d ℂ) (x : d → ℂ) :
    ‖star x ⬝ᵥ M *ᵥ x‖ ≤ ↑(Fintype.card d) * ‖M‖ * ∑ i : d, ‖x i‖ ^ 2 := by
  simp only [dotProduct, mulVec, star]
  calc ‖∑ i, (starRingEnd ℂ) (x i) * ∑ j, M i j * x j‖
      ≤ ∑ i, ‖(starRingEnd ℂ) (x i) * ∑ j, M i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x i‖ * (‖M‖ * ∑ j, ‖x j‖) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_mul, Complex.norm_conj]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc ‖∑ j, M i j * x j‖
            ≤ ∑ j, ‖M i j * x j‖ := norm_sum_le _ _
          _ = ∑ j, ‖M i j‖ * ‖x j‖ := by congr 1; ext j; exact norm_mul _ _
          _ ≤ ∑ j, ‖M‖ * ‖x j‖ := Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (norm_entry_le_entrywise_sup_norm M) (norm_nonneg _)
          _ = ‖M‖ * ∑ j, ‖x j‖ := by rw [Finset.mul_sum]
    _ ≤ ↑(Fintype.card d) * ‖M‖ * ∑ i : d, ‖x i‖ ^ 2 := by
        have h1 : ∑ i : d, ‖x i‖ * (‖M‖ * ∑ j : d, ‖x j‖) =
            ‖M‖ * (∑ i : d, ‖x i‖) ^ 2 := by
          rw [sq]; simp_rw [mul_comm (‖M‖) _, ← Finset.sum_mul]; ring
        rw [h1]
        have h2 := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _
          (s := Finset.univ) (f := fun i => ‖x i‖)
        rw [Finset.card_univ] at h2
        calc ‖M‖ * (∑ i : d, ‖x i‖) ^ 2
            ≤ ‖M‖ * (↑(Fintype.card d) * ∑ i : d, ‖x i‖ ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ = ↑(Fintype.card d) * ‖M‖ * ∑ i : d, ‖x i‖ ^ 2 := by ring

/-- Hermitian quadratic form is real: `Im(⟨x, Hx⟩) = 0` for Hermitian H.
    Proved via involution pairing: terms (i,j) and (j,i) contribute conjugate values. -/
private lemma hermitian_quadratic_im_zero {d : Type*} [Fintype d]
    (H : Matrix d d ℂ) (hH : H.IsHermitian) (x : d → ℂ) :
    (star x ⬝ᵥ H *ᵥ x).im = 0 := by
  simp only [dotProduct, mulVec]
  change (∑ i : d, (star x) i * ∑ j : d, H i j * x j).im = 0
  rw [show (∑ i : d, (star x) i * ∑ j : d, H i j * x j).im =
    ∑ i : d, ((star x) i * ∑ j : d, H i j * x j).im from
    map_sum Complex.imAddGroupHom _ _]
  simp_rw [Finset.mul_sum,
    show ∀ i : d, (∑ j : d, (star x) i * (H i j * x j)).im =
      ∑ j : d, ((star x) i * (H i j * x j)).im from
      fun i => map_sum Complex.imAddGroupHom _ _]
  rw [← Finset.sum_product']
  let σ : d × d → d × d := fun p => (p.2, p.1)
  apply Finset.sum_involution (fun a _ => σ a)
  · intro ⟨i, j⟩ _
    set z := (star x) i * (H i j * x j)
    suffices heq : ((star x) j * (H j i * x i)) = starRingEnd ℂ z by
      rw [heq, Complex.conj_im, add_neg_cancel]
    rw [map_mul, show (starRingEnd ℂ) ((star x) i) = x i from star_star (x i),
      map_mul, show (starRingEnd ℂ) (H i j) = H j i from congr_fun (congr_fun hH j) i]
    change (starRingEnd ℂ) (x j) * (H j i * x i) = x i * (H j i * (starRingEnd ℂ) (x j))
    ring
  · intro ⟨i, j⟩ _ hne heq
    apply hne
    have : i = j := (Prod.mk.inj heq).2
    subst this
    change ((starRingEnd ℂ) (x i) * (H i i * x i)).im = 0
    rw [show (starRingEnd ℂ) (x i) * (H i i * x i) = H i i * ((starRingEnd ℂ) (x i) * x i)
      from by ring, Complex.normSq_eq_conj_mul_self.symm]
    have hii_real : (H i i).im = 0 :=
      Complex.conj_eq_iff_im.mp (congr_fun (congr_fun hH i) i)
    simp [Complex.mul_im, hii_real]
  · intro ⟨i, j⟩ _
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  · intro ⟨i, j⟩ _; rfl

/-- Hermitian shift to PSD: for Hermitian H, `H + c·I` is PSD when `c ≥ d·‖H‖`.
    Uses `norm_quadratic_form_le` for the lower bound on the quadratic form. -/
private lemma hermitian_shift_psd {d : Type*} [Fintype d] [DecidableEq d] {H : Matrix d d ℂ}
    (hH : H.IsHermitian) (c : ℝ) (hc : ↑(Fintype.card d) * ‖H‖ ≤ c) :
    (H + (↑c : ℂ) • (1 : Matrix d d ℂ)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · have : ((↑c : ℂ) • (1 : Matrix d d ℂ)).IsHermitian := by
      change ((↑c : ℂ) • (1 : Matrix d d ℂ))ᴴ = (↑c : ℂ) • 1
      rw [conjTranspose_smul, isHermitian_one]; congr 1; exact Complex.conj_ofReal c
    exact hH.add this
  · intro x
    rw [add_mulVec, dotProduct_add,
      show ((↑c : ℂ) • (1 : Matrix d d ℂ)) *ᵥ x = (↑c : ℂ) • x from by
        rw [smul_mulVec (↑c : ℂ) 1 x, one_mulVec],
      dotProduct_smul]
    have hxx_eq : star x ⬝ᵥ x = ↑(∑ i : d, ‖x i‖ ^ 2 : ℝ) := by
      simp only [dotProduct]; rw [Complex.ofReal_sum]
      congr 1; ext i
      change (starRingEnd ℂ) (x i) * x i = ↑(‖x i‖ ^ 2)
      rw [Complex.normSq_eq_conj_mul_self.symm, Complex.sq_norm]
    rw [hxx_eq]
    set S := ∑ i : d, ‖x i‖ ^ 2
    have hS_nn : (0 : ℝ) ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hqf_im := hermitian_quadratic_im_zero H hH x
    have hqf_re_bound : -(↑(Fintype.card d) * ‖H‖ * S) ≤ (star x ⬝ᵥ H *ᵥ x).re := by
      have hle := norm_quadratic_form_le H x
      calc -(↑(Fintype.card d) * ‖H‖ * S) ≤ -‖star x ⬝ᵥ H *ᵥ x‖ := neg_le_neg hle
        _ ≤ -|Complex.re (star x ⬝ᵥ H *ᵥ x)| := neg_le_neg (Complex.abs_re_le_norm _)
        _ ≤ (star x ⬝ᵥ H *ᵥ x).re := neg_abs_le _
    have hcS_re : ((↑c : ℂ) * (↑S : ℂ)).re = c * S := by simp
    have hcS_im : ((↑c : ℂ) * (↑S : ℂ)).im = 0 := by simp
    rw [Complex.nonneg_iff, smul_eq_mul] at *
    exact ⟨by rw [Complex.add_re, hcS_re]; linarith [mul_le_mul_of_nonneg_right hc hS_nn],
           by rw [Complex.add_im, hcS_im]; linarith⟩

/-- `trace(M).re ≤ d · ‖M‖` for any `d×d` complex matrix. -/
private lemma trace_re_le_dim_mul_norm {d : Type*} [Fintype d] (M : Matrix d d ℂ) :
    M.trace.re ≤ ↑(Fintype.card d) * ‖M‖ := by
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  calc ∑ i : d, (M i i).re
      ≤ ∑ i : d, ‖M i i‖ := Finset.sum_le_sum fun i _ => Complex.re_le_norm _
    _ ≤ ∑ i : d, ‖M‖ := Finset.sum_le_sum fun i _ => norm_entry_le_entrywise_sup_norm M
    _ = ↑(Fintype.card d) * ‖M‖ := by simp [Finset.sum_const, nsmul_eq_mul]

private lemma trace_one_re {d : Type*} [Fintype d] [DecidableEq d] :
    (1 : Matrix d d ℂ).trace.re = (↑(Fintype.card d) : ℝ) := by
  simp [Matrix.trace, Matrix.diag, Finset.sum_const, nsmul_eq_mul]

private lemma trace_add_smul_one_re {d : Type*} [Fintype d] [DecidableEq d] (H : Matrix d d ℂ)
    (c : ℝ) :
    (H + (↑c : ℂ) • (1 : Matrix d d ℂ)).trace.re =
    H.trace.re + c * ↑(Fintype.card d) := by
  simp

/-- Core Hermitian bound: `‖L(H)‖ ≤ d(2d+1)·‖H‖` for Hermitian H and sub-TP L.
    Uses shift trick: L(H) = L(H+c·I) - c·L(I) where c = d·‖H‖. -/
private lemma hermitian_norm_bound {d : Type*} [Fintype d]
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hpsd : ∀ (M : Matrix d d ℂ), M.PosSemidef → (L M).PosSemidef)
    (hstp : ∀ (M : Matrix d d ℂ), M.PosSemidef → (L M).trace.re ≤ M.trace.re)
    (H : Matrix d d ℂ) (hH : H.IsHermitian) :
    ‖L H‖ ≤ ↑(Fintype.card d) * (2 * ↑(Fintype.card d) + 1) * ‖H‖ := by
  classical
  set c := (↑(Fintype.card d) : ℝ) * ‖H‖ with hc_def
  have hc_nn : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hdecomp : L H = L (H + (↑c : ℂ) • 1) - (↑c : ℂ) • L 1 := by
    rw [map_add, map_smul]; simp
  rw [hdecomp]
  have hpsd_shift := hermitian_shift_psd hH c le_rfl
  have hpsd_one : (1 : Matrix d d ℂ).PosSemidef := PosSemidef.one
  calc ‖L (H + (↑c : ℂ) • 1) - (↑c : ℂ) • L 1‖
      ≤ ‖L (H + (↑c : ℂ) • 1)‖ + ‖(↑c : ℂ) • L 1‖ := norm_sub_le _ _
    _ ≤ ‖L (H + (↑c : ℂ) • 1)‖ + c * ‖L 1‖ := by
        rw [norm_smul, Complex.norm_of_nonneg (by exact_mod_cast hc_nn)]
    _ ≤ (H + (↑c : ℂ) • 1).trace.re + c * (1 : Matrix d d ℂ).trace.re := by
        gcongr
        · exact le_trans (psd_norm_le_trace (hpsd _ hpsd_shift)) (hstp _ hpsd_shift)
        · exact le_trans (psd_norm_le_trace (hpsd 1 hpsd_one)) (hstp 1 hpsd_one)
    _ ≤ ↑(Fintype.card d) * ‖H‖ + c * ↑(Fintype.card d) + c * ↑(Fintype.card d) := by
        rw [trace_add_smul_one_re, trace_one_re]
        linarith [trace_re_le_dim_mul_norm H]
    _ = ↑(Fintype.card d) * (2 * ↑(Fintype.card d) + 1) * ‖H‖ := by rw [hc_def]; ring

/-- For instrument branches and PSD input M, ∑ᵦ ‖branch b M‖ ≤ trace(M).re. -/
private theorem instrument_psd_l1_le
    {d : Type*} [Fintype d] {β : Type}
    (branch : β → (Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ))
    (hpsd : ∀ b (M : Matrix d d ℂ), M.PosSemidef → (branch b M).PosSemidef)
    (hsum : ∀ (M : Matrix d d ℂ), Summable (fun b => branch b M))
    (hstp : ∀ (M : Matrix d d ℂ), M.PosSemidef →
      (∑' b, (branch b M).trace).re ≤ M.trace.re)
    (M : Matrix d d ℂ) (hM : M.PosSemidef) :
    ∑' b, ‖branch b M‖ ≤ M.trace.re :=
  calc ∑' b, ‖branch b M‖
      ≤ ∑' b, (branch b M).trace.re :=
        Summable.tsum_le_tsum (fun b => psd_norm_le_trace (hpsd b M hM))
          (summable_norm_iff.mpr (hsum M)) (trace_re_summable (hsum M))
    _ = (∑' b, (branch b M).trace).re :=
        (Complex.re_tsum (trace_summable (hsum M))).symm
    _ ≤ M.trace.re := hstp M hM

/-- L1 Hermitian bound for instruments: `∑ᵦ ‖Lᵦ(H)‖ ≤ d(2d+1)·‖H‖`. -/
private lemma hermitian_l1_bound {d : Type*} [Fintype d] {β : Type}
    (branch : β → (Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ))
    (hpsd : ∀ b (M : Matrix d d ℂ), M.PosSemidef → (branch b M).PosSemidef)
    (hsum : ∀ (M : Matrix d d ℂ), Summable (fun b => branch b M))
    (hstp : ∀ (M : Matrix d d ℂ), M.PosSemidef →
      (∑' b, (branch b M).trace).re ≤ M.trace.re)
    (H : Matrix d d ℂ) (hH : H.IsHermitian) :
    ∑' b, ‖branch b H‖ ≤ ↑(Fintype.card d) * (2 * ↑(Fintype.card d) + 1) * ‖H‖ := by
  classical
  set c := (↑(Fintype.card d) : ℝ) * ‖H‖ with hc_def
  have hc_nn : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hpsd_shift := hermitian_shift_psd hH c le_rfl
  have hpsd_one : (1 : Matrix d d ℂ).PosSemidef := PosSemidef.one
  -- branch b H = branch b (H + c·I) - c · branch b I
  have hdecomp : ∀ b, branch b H = branch b (H + (↑c : ℂ) • 1) - (↑c : ℂ) • branch b 1 := by
    intro b; rw [map_add, map_smul]; simp
  -- ‖branch b H‖ ≤ ‖branch b (H+c·I)‖ + c·‖branch b I‖
  have hle : ∀ b, ‖branch b H‖ ≤ ‖branch b (H + (↑c : ℂ) • 1)‖ + c * ‖branch b 1‖ := by
    intro b; rw [hdecomp b]
    calc ‖branch b (H + (↑c : ℂ) • 1) - (↑c : ℂ) • branch b 1‖
        ≤ ‖branch b (H + (↑c : ℂ) • 1)‖ + ‖(↑c : ℂ) • branch b 1‖ := norm_sub_le _ _
      _ = ‖branch b (H + (↑c : ℂ) • 1)‖ + c * ‖branch b 1‖ := by
          rw [norm_smul, Complex.norm_of_nonneg (by exact_mod_cast hc_nn)]
  -- Summability of the bounding terms
  have hsum_shift := summable_norm_iff.mpr (hsum (H + (↑c : ℂ) • 1))
  have hsum_one := summable_norm_iff.mpr (hsum 1)
  calc ∑' b, ‖branch b H‖
      ≤ ∑' b, (‖branch b (H + (↑c : ℂ) • 1)‖ + c * ‖branch b 1‖) :=
        Summable.tsum_le_tsum hle (summable_norm_iff.mpr (hsum H))
          (hsum_shift.add (hsum_one.mul_left c))
    _ = (∑' b, ‖branch b (H + (↑c : ℂ) • 1)‖) + c * (∑' b, ‖branch b 1‖) := by
        rw [Summable.tsum_add hsum_shift (hsum_one.mul_left c), tsum_mul_left]
    _ ≤ (H + (↑c : ℂ) • 1).trace.re + c * (1 : Matrix d d ℂ).trace.re := by
        gcongr
        · exact instrument_psd_l1_le branch hpsd hsum hstp _ hpsd_shift
        · exact instrument_psd_l1_le branch hpsd hsum hstp 1 hpsd_one
    _ ≤ ↑(Fintype.card d) * ‖H‖ + c * ↑(Fintype.card d) + c * ↑(Fintype.card d) := by
        rw [trace_add_smul_one_re, trace_one_re]
        linarith [trace_re_le_dim_mul_norm H]
    _ = ↑(Fintype.card d) * (2 * ↑(Fintype.card d) + 1) * ‖H‖ := by rw [hc_def]; ring

/-- Hermitian decomposition helper: `‖(2⁻¹)‖ * 2 = 1` for complex inverse of 2. -/
private lemma inv2_norm_mul_2 : ‖(2 : ℂ)⁻¹‖ * 2 = 1 := by
  have h : (2 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹) := by push_cast; norm_num
  rw [h, Complex.norm_of_nonneg (by positivity)]; norm_num

/-- Every complex matrix is `H₁ + (-i) • H₂` with Hermitian `H₁`, `H₂` of norm at
most its own. -/
private lemma exists_hermitian_decomp {d : Type*} [Fintype d] (M : Matrix d d ℂ) :
    ∃ H₁ H₂ : Matrix d d ℂ, H₁.IsHermitian ∧ H₂.IsHermitian ∧
      ‖H₁‖ ≤ ‖M‖ ∧ ‖H₂‖ ≤ ‖M‖ ∧ M = H₁ + (-Complex.I) • H₂ := by
  refine ⟨(2 : ℂ)⁻¹ • (M + Mᴴ), Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ)), ?_, ?_, ?_, ?_, ?_⟩
  · change ((2 : ℂ)⁻¹ • (M + Mᴴ))ᴴ = (2 : ℂ)⁻¹ • (M + Mᴴ)
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]; simp; abel
  · change (Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ)))ᴴ = Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ))
    rw [conjTranspose_smul, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose,
      Complex.star_def, Complex.conj_I,
      show (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ from by rw [map_inv₀, map_ofNat]]
    simp only [neg_smul, smul_sub]; abel
  · calc ‖(2 : ℂ)⁻¹ • (M + Mᴴ)‖ = ‖(2 : ℂ)⁻¹‖ * ‖M + Mᴴ‖ := norm_smul _ _
      _ ≤ ‖(2 : ℂ)⁻¹‖ * (‖M‖ + ‖Mᴴ‖) := by gcongr; exact norm_add_le _ _
      _ = ‖(2 : ℂ)⁻¹‖ * 2 * ‖M‖ := by rw [norm_conjTranspose]; ring
      _ = ‖M‖ := by rw [inv2_norm_mul_2, one_mul]
  · calc ‖Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ))‖ = ‖(2 : ℂ)⁻¹‖ * ‖M - Mᴴ‖ := by
          rw [norm_smul, Complex.norm_I, one_mul, norm_smul]
      _ ≤ ‖(2 : ℂ)⁻¹‖ * (‖M‖ + ‖Mᴴ‖) := by gcongr; exact norm_sub_le _ _
      _ = ‖(2 : ℂ)⁻¹‖ * 2 * ‖M‖ := by rw [norm_conjTranspose]; ring
      _ = ‖M‖ := by rw [inv2_norm_mul_2, one_mul]
  · rw [smul_smul, show (-Complex.I) * Complex.I = 1 from by rw [neg_mul, Complex.I_mul_I]; simp,
      one_smul, ← smul_add,
      show M + Mᴴ + (M - Mᴴ) = (2 : ℂ) • M from by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ (two_ne_zero)]; simp

/-- Uniform operator norm bound for a single branch of a PSD-preserving sub-TP map.
    Every such map L satisfies `‖L(M)‖ ≤ C(d) · ‖M‖` where `C(d) = 2d(2d+1)`.
    Proved via Hermitian shift decomposition. -/
private def subTP_opNorm_bound (d : Type*) [Fintype d] : ℝ :=
  2 * ↑(Fintype.card d) * (2 * ↑(Fintype.card d) + 1)
private theorem subTP_opNorm_le
    {d : Type*} [Fintype d]
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hpsd : ∀ (M : Matrix d d ℂ), M.PosSemidef → (L M).PosSemidef)
    (hstp : ∀ (M : Matrix d d ℂ), M.PosSemidef → (L M).trace.re ≤ M.trace.re)
    (M : Matrix d d ℂ) :
    ‖L M‖ ≤ subTP_opNorm_bound d * ‖M‖ := by
  obtain ⟨H₁, H₂, hH₁, hH₂, hn₁, hn₂, hM⟩ := exists_hermitian_decomp M
  have hc : (0 : ℝ) ≤ Fintype.card d * (2 * Fintype.card d + 1) := by positivity
  calc ‖L M‖ ≤ ‖L H₁‖ + ‖L H₂‖ := by
        rw [hM, map_add, map_smul]
        exact (norm_add_le _ _).trans_eq (by rw [norm_smul]; simp)
    _ ≤ ↑(Fintype.card d) * (2 * ↑(Fintype.card d) + 1) * ‖H₁‖ +
        ↑(Fintype.card d) * (2 * ↑(Fintype.card d) + 1) * ‖H₂‖ :=
        add_le_add (hermitian_norm_bound L hpsd hstp H₁ hH₁)
          (hermitian_norm_bound L hpsd hstp H₂ hH₂)
    _ ≤ subTP_opNorm_bound d * ‖M‖ := by
        unfold subTP_opNorm_bound
        linarith [mul_le_mul_of_nonneg_left hn₁ hc, mul_le_mul_of_nonneg_left hn₂ hc]

/-- Total L1-norm bound for all branches of an instrument.
    `∑ᵦ ‖Lᵦ(M)‖ ≤ C(d) · ‖M‖` where `C(d) = 2d(2d+1)`.
    Proved via Hermitian shift decomposition, same as `subTP_opNorm_le`. -/
private def instrument_l1_bound (d : Type*) [Fintype d] : ℝ := subTP_opNorm_bound d
private theorem instrument_l1_le
    {d : Type*} [Fintype d] {β : Type}
    (branch : β → (Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ))
    (hpsd : ∀ b (M : Matrix d d ℂ), M.PosSemidef → (branch b M).PosSemidef)
    (hsum : ∀ (M : Matrix d d ℂ), Summable (fun b => branch b M))
    (hstp : ∀ (M : Matrix d d ℂ), M.PosSemidef →
      (∑' b, (branch b M).trace).re ≤ M.trace.re)
    (M : Matrix d d ℂ) :
    ∑' b, ‖branch b M‖ ≤ instrument_l1_bound d * ‖M‖ := by
  obtain ⟨H₁, H₂, hH₁, hH₂, hn₁, hn₂, hM⟩ := exists_hermitian_decomp M
  have hc : (0 : ℝ) ≤ Fintype.card d * (2 * Fintype.card d + 1) := by positivity
  have hle : ∀ b, ‖branch b M‖ ≤ ‖branch b H₁‖ + ‖branch b H₂‖ := fun b => by
    rw [hM, map_add, map_smul]
    exact (norm_add_le _ _).trans_eq (by rw [norm_smul]; simp)
  have hs₁ := summable_norm_iff.mpr (hsum H₁)
  have hs₂ := summable_norm_iff.mpr (hsum H₂)
  calc ∑' b, ‖branch b M‖
      ≤ ∑' b, (‖branch b H₁‖ + ‖branch b H₂‖) :=
        Summable.tsum_le_tsum hle (summable_norm_iff.mpr (hsum M)) (hs₁.add hs₂)
    _ = (∑' b, ‖branch b H₁‖) + (∑' b, ‖branch b H₂‖) := hs₁.tsum_add hs₂
    _ ≤ ↑(Fintype.card d) * (2 * ↑(Fintype.card d) + 1) * ‖H₁‖ +
        ↑(Fintype.card d) * (2 * ↑(Fintype.card d) + 1) * ‖H₂‖ :=
        add_le_add (hermitian_l1_bound branch hpsd hsum hstp H₁ hH₁)
          (hermitian_l1_bound branch hpsd hsum hstp H₂ hH₂)
    _ ≤ instrument_l1_bound d * ‖M‖ := by
        unfold instrument_l1_bound subTP_opNorm_bound
        linarith [mul_le_mul_of_nonneg_left hn₁ hc, mul_le_mul_of_nonneg_left hn₂ hc]

/-! ## Bind -/

/-- The family of composites `(f a).branch b (I.branch a ρ)` over the first
outcome `a` is summable. -/
theorem QComp.bind_summable (I : QComp d α) (f : α → QComp d β)
    (b : β) (ρ : Matrix d d ℂ) :
    Summable (fun a => (f a).branch b (I.branch a ρ)) :=
  Summable.of_norm_bounded
    (g := fun a => subTP_opNorm_bound d * ‖I.branch a ρ‖)
    ((summable_norm_iff (E := Matrix d d ℂ)).mpr
      (I.branch_summable ρ) |>.hasSum.mul_left (subTP_opNorm_bound d) |>.summable)
    (fun a => subTP_opNorm_le ((f a).branch b)
      (fun M hM => (f a).branch_psd b M hM)
      (fun M hM => (f a).single_stp b M hM)
      (I.branch a ρ))

/-- Joint summability of the uncurried family for Fubini in `qbind_assoc`. -/
theorem QComp.bind_summable_uncurry (I : QComp d α) (f : α → QComp d β)
    (g : β → QComp d γ) (c : γ) (ρ : Matrix d d ℂ) :
    Summable (Function.uncurry fun a b =>
      (g b).branch c ((f a).branch b (I.branch a ρ))) := by
  -- Norm bound per (a,b): ‖F(a,b)‖ ≤ C · ‖(f a).branch b (I.branch a ρ)‖
  have hF_le : ∀ (p : α × β),
      ‖(Function.uncurry fun a b => (g b).branch c ((f a).branch b (I.branch a ρ))) p‖ ≤
      subTP_opNorm_bound d * ‖(f p.1).branch p.2 (I.branch p.1 ρ)‖ :=
    fun ⟨a, b⟩ => subTP_opNorm_le ((g b).branch c)
      (fun M hM => (g b).branch_psd c M hM)
      (fun M hM => (g b).single_stp c M hM)
      ((f a).branch b (I.branch a ρ))
  -- Intermediate norm family is summable over the product (via summable_prod_of_nonneg)
  have hG_norm_summable : Summable (fun (p : α × β) =>
      ‖(f p.1).branch p.2 (I.branch p.1 ρ)‖) := by
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    exact ⟨fun a => summable_norm_iff.mpr ((f a).branch_summable (I.branch a ρ)),
      Summable.of_nonneg_of_le
        (fun a => tsum_nonneg (fun b => norm_nonneg _))
        (fun a => instrument_l1_le (f a).branch (f a).branch_psd
          (f a).branch_summable (f a).branch_stp (I.branch a ρ))
        ((summable_norm_iff (E := Matrix d d ℂ)).mpr
          (I.branch_summable ρ) |>.hasSum.mul_left (instrument_l1_bound d) |>.summable)⟩
  -- Summable by comparison with the bounding function
  exact Summable.of_norm_bounded
    (g := fun p => subTP_opNorm_bound d * ‖(f p.1).branch p.2 (I.branch p.1 ρ)‖)
    (hG_norm_summable.hasSum.mul_left (subTP_opNorm_bound d) |>.summable)
    hF_le

/-- Joint summability of the (a,b)-family (without the outer g), used for
branch_summable and for `qbind` reasoning (e.g. `localOp₁` functoriality). -/
theorem QComp.bind_uncurry_summable (I : QComp d α) (f : α → QComp d β)
    (ρ : Matrix d d ℂ) :
    Summable (Function.uncurry fun a b => (f a).branch b (I.branch a ρ)) := by
  rw [show (Function.uncurry fun a b => (f a).branch b (I.branch a ρ)) =
      (fun (p : α × β) => (f p.1).branch p.2 (I.branch p.1 ρ)) from rfl]
  exact summable_norm_iff.mp
    ((summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
      ⟨fun a => summable_norm_iff.mpr ((f a).branch_summable (I.branch a ρ)),
       Summable.of_nonneg_of_le
        (fun a => tsum_nonneg (fun b => norm_nonneg _))
        (fun a => instrument_l1_le (f a).branch (f a).branch_psd
          (f a).branch_summable (f a).branch_stp (I.branch a ρ))
        ((summable_norm_iff (E := Matrix d d ℂ)).mpr
          (I.branch_summable ρ) |>.hasSum.mul_left (instrument_l1_bound d) |>.summable)⟩)

/-- Kleisli composition of instruments: the branch at `b` maps `ρ` to
`∑' a, (f a).branch b (I.branch a ρ)`. -/
def QComp.qbind (I : QComp d α) (f : α → QComp d β) : QComp d β where
  branch b :=
    { toFun := fun ρ => ∑' a, (f a).branch b (I.branch a ρ)
      map_add' := fun ρ₁ ρ₂ => by
        simp only [map_add]
        exact (bind_summable I f b ρ₁).tsum_add (bind_summable I f b ρ₂)
      map_smul' := fun c ρ => by
        simp only [map_smul]
        exact tsum_const_smul'' c
    }
  branch_psd b ρ hρ :=
    tsum_posSemidef
      (fun a => (f a).branch_psd b _ (I.branch_psd a ρ hρ))
      (bind_summable I f b ρ)
  branch_summable ρ := by
    -- From the joint (a,b)-summability, swap to get the b-marginal.
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    have huncurry := bind_uncurry_summable I f ρ
    -- Swap: Summable (fun (b, a) => (f a).branch b (I.branch a ρ))
    have hswap : Summable (fun p : β × α =>
        (f p.2).branch p.1 (I.branch p.2 ρ)) := by
      have : Summable ((fun p : α × β => (f p.1).branch p.2 (I.branch p.1 ρ)) ∘
          (Equiv.prodComm β α)) := by
        rw [show (fun p : α × β => (f p.1).branch p.2 (I.branch p.1 ρ)) =
            Function.uncurry (fun a b => (f a).branch b (I.branch a ρ)) from rfl]
        exact (Equiv.prodComm β α).summable_iff.mpr huncurry
      simp only [Equiv.prodComm_apply, Function.comp_def] at this
      exact this
    -- b-marginal: Summable (fun b => ∑' a, ...)
    exact hswap.prod
  branch_stp ρ hρ := by
    -- Push trace through inner tsum:
    have htrace_inner : ∀ b, (∑' a, (f a).branch b (I.branch a ρ)).trace =
        ∑' a, ((f a).branch b (I.branch a ρ)).trace := fun b =>
      trace_tsum (bind_summable I f b ρ)
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [htrace_inner]
    -- Swap sums via Fubini for the trace family:
    -- ∑' b, ∑' a, g(a,b) = ∑' a, ∑' b, g(a,b) where g(a,b) = trace((f a).branch b (...))
    have htrace_uncurry : Summable (Function.uncurry fun a b =>
        ((f a).branch b (I.branch a ρ)).trace) :=
      trace_summable (bind_uncurry_summable I f ρ)
    rw [htrace_uncurry.tsum_comm'
      (fun a => trace_summable ((f a).branch_summable (I.branch a ρ)))
      (fun b => trace_summable (bind_summable I f b ρ))]
    -- Goal: (∑' a, ∑' b, ((f a).branch b (I.branch a ρ)).trace).re ≤ ρ.trace.re
    -- = (∑' a, (∑' b, (f a).branch b (I.branch a ρ)).trace).re
    -- where the inner sum uses trace_tsum backwards.
    conv_lhs =>
      arg 1; arg 1; ext a
      rw [(trace_tsum ((f a).branch_summable (I.branch a ρ))).symm]
    -- Now: (∑' a, (∑' b, (f a).branch b (I.branch a ρ)).trace).re ≤ ρ.trace.re
    -- Apply .re via reCLM, then use (f a).branch_stp and I.branch_stp
    have hfa_stp : ∀ a, (∑' b, (f a).branch b (I.branch a ρ)).trace.re ≤
        (I.branch a ρ).trace.re := by
      intro a
      rw [trace_tsum ((f a).branch_summable (I.branch a ρ))]
      exact (f a).branch_stp (I.branch a ρ) (I.branch_psd a ρ hρ)
    have houter_summable : Summable (fun a =>
        (∑' b, (f a).branch b (I.branch a ρ)).trace) := by
      have : Summable (fun a => ∑' b, (f a).branch b (I.branch a ρ)) := by
        have huncurry := bind_uncurry_summable I f ρ
        exact huncurry.prod
      exact trace_summable this
    rw [Complex.re_tsum houter_summable]
    calc ∑' a, (∑' b, (f a).branch b (I.branch a ρ)).trace.re
        ≤ ∑' a, (I.branch a ρ).trace.re :=
          Summable.tsum_le_tsum hfa_stp
            (houter_summable.map Complex.reAddGroupHom Complex.continuous_re)
            (trace_re_summable (I.branch_summable ρ))
      _ = (∑' a, (I.branch a ρ).trace).re :=
          (Complex.re_tsum (trace_summable (I.branch_summable ρ))).symm
      _ ≤ ρ.trace.re := I.branch_stp ρ hρ

/-! ## Monad Laws -/

/-- Left unit law: `qpure a` followed by `f` is `f a`. -/
theorem QComp.qpure_qbind (a : α) (f : α → QComp d β) :
    QComp.qbind (QComp.qpure a) f = f a := by
  apply QComp.ext_fun; intro b ρ
  change ∑' a', (f a').branch b ((QComp.qpure a).branch a' ρ) = (f a).branch b ρ
  simp only [QComp.qpure]
  rw [tsum_eq_single a (fun a' ha' => by simp [ha', map_zero])]
  simp

/-- Right unit law: `I` followed by `qpure` is `I`. -/
theorem QComp.qbind_qpure (I : QComp d α) :
    QComp.qbind I QComp.qpure = I := by
  apply QComp.ext_fun; intro b ρ
  change ∑' a, (QComp.qpure a).branch b (I.branch a ρ) = I.branch b ρ
  simp only [QComp.qpure]
  rw [tsum_eq_single b (fun a ha => by simp [Ne.symm ha])]
  simp

/-- Associativity of Kleisli composition of instruments. -/
theorem QComp.qbind_assoc (I : QComp d α) (f : α → QComp d β)
    (g : β → QComp d γ) :
    QComp.qbind (QComp.qbind I f) g =
    QComp.qbind I (fun a => QComp.qbind (f a) g) := by
  apply QComp.ext_fun; intro c ρ
  change ∑' b, (g b).branch c (∑' a, (f a).branch b (I.branch a ρ)) =
       ∑' a, ∑' b, (g b).branch c ((f a).branch b (I.branch a ρ))
  have hdist : ∀ b', (g b').branch c (∑' a, (f a).branch b' (I.branch a ρ)) =
      ∑' a, (g b').branch c ((f a).branch b' (I.branch a ρ)) :=
    fun b' => ContinuousLinearMap.map_tsum ((g b').branch c).toContinuousLinearMap
      (QComp.bind_summable I f b' ρ)
  simp_rw [hdist]
  exact (QComp.bind_summable_uncurry I f g c ρ).tsum_comm'
    (fun a => QComp.bind_summable (f a) g c (I.branch a ρ))
    (fun b => (QComp.bind_summable I f b ρ).map ((g b).branch c).toContinuousLinearMap
      ((g b).branch c).toContinuousLinearMap.continuous)

/-! ## Monad Instance -/

/-- Instruments form a monad with unit `QComp.qpure` and bind `QComp.qbind`. -/
instance : Monad (QComp d) where
  pure := QComp.qpure
  bind := QComp.qbind

/-- The instrument monad satisfies the monad laws. -/
instance : LawfulMonad (QComp d) := LawfulMonad.mk'
  (id_map := fun m => QComp.qbind_qpure m)
  (pure_bind := fun a f => QComp.qpure_qbind a f)
  (bind_assoc := fun m f g => QComp.qbind_assoc m f g)

/-! ## Bind with Fail -/

/-- Composing any instrument with the failing continuation fails. -/
theorem QComp.qbind_fail (c : QComp d α) :
    QComp.qbind c (fun _ => (QComp.qfail : QComp d β)) = QComp.qfail := by
  ext
  simp [QComp.qbind, QComp.qfail]

/-- The failing instrument followed by any continuation fails. -/
theorem QComp.qfail_qbind (f : α → QComp d β) :
    QComp.qbind (QComp.qfail : QComp d α) f = QComp.qfail := by
  apply QComp.ext_fun; intro b ρ
  change ∑' a, (f a).branch b (QComp.qfail.branch a ρ) = 0
  simp only [QComp.qfail, LinearMap.zero_apply, map_zero, tsum_zero]

/-! ## Parallel Composition on Sum -/

/-- The Kleisli arrow on a sum type that runs `f` on a left input and `g` on a
right input, tagging the outcome with the same side. -/
def QComp.mapSum (f : α → QComp d β) (g : γ → QComp d δ) :
    (α ⊕ γ) → QComp d (β ⊕ δ)
  | .inl a => QComp.qbind (f a) (fun b => QComp.qpure (.inl b))
  | .inr c => QComp.qbind (g c) (fun d' => QComp.qpure (.inr d'))

/-- `QComp.mapSum` on a left input. -/
theorem QComp.mapSum_inl (f : α → QComp d β) (g : γ → QComp d δ) (a : α) :
    QComp.mapSum f g (.inl a) = f a >>= fun b => pure (.inl b) := rfl

/-- `QComp.mapSum` on a right input. -/
theorem QComp.mapSum_inr (f : α → QComp d β) (g : γ → QComp d δ) (c : γ) :
    QComp.mapSum f g (.inr c) = g c >>= fun d' => pure (.inr d') := rfl

/-- `QComp.mapSum` of the units is the unit on the sum type. -/
theorem QComp.mapSum_pure_pure :
    QComp.mapSum (QComp.qpure : α → QComp d α)
      (QComp.qpure : β → QComp d β) = QComp.qpure := by
  funext x; cases x with
  | inl a => exact QComp.qpure_qbind a _
  | inr b => exact QComp.qpure_qbind b _

/-- `QComp.mapSum qpure` preserves Kleisli composition of right arrows. -/
theorem QComp.mapSum_pure_kleisli (f : β → QComp d γ) (g : γ → QComp d δ) :
    (fun x : α ⊕ β => QComp.mapSum QComp.qpure f x >>=
      QComp.mapSum QComp.qpure g) =
    QComp.mapSum QComp.qpure (fun b => f b >>= g) := by
  funext x; cases x with
  | inl a =>
    -- Both sides reduce to qpure (.inl a) via mapSum + qpure_qbind
    change QComp.qbind (QComp.mapSum QComp.qpure f (.inl a))
      (QComp.mapSum QComp.qpure g) = _
    simp only [QComp.mapSum]
    rw [QComp.qpure_qbind, QComp.qpure_qbind]; rfl
  | inr b =>
    -- LHS: bind(bind(f b)(pure ∘ inr))(mapSum pure g)
    -- = bind(f b)(fun c => bind(pure(inr c))(mapSum pure g))  [assoc]
    -- = bind(f b)(fun c => mapSum pure g (inr c))  [pure_bind]
    -- = bind(f b)(fun c => bind(g c)(pure ∘ inr))  [mapSum def]
    -- = bind(f b >>= g)(pure ∘ inr)  [assoc]
    -- = RHS
    change QComp.qbind (QComp.mapSum QComp.qpure f (.inr b))
      (QComp.mapSum QComp.qpure g) =
      QComp.qbind (QComp.qbind (f b) g) (fun d' => QComp.qpure (.inr d'))
    simp only [QComp.mapSum]
    rw [QComp.qbind_assoc]
    conv_rhs => rw [QComp.qbind_assoc]
    congr 1; funext c
    rw [QComp.qpure_qbind]; rfl

/-! ## Probability and Distance Helpers -/

/-- Probability of outcome `true` for `I : QComp d Bool` at state `ρ`. -/
def prTrue_Q (I : QComp d Bool) (ρ : DensityMatrix d) : ℝ≥0∞ :=
  ENNReal.ofReal ((I.branch true ρ.val).trace.re)

/-- The distance `(a - b) ⊔ (b - a)` between two extended nonnegative reals. -/
def absDiff (a b : ℝ≥0∞) : ℝ≥0∞ := (a - b) ⊔ (b - a)

/-- `absDiff a a = 0`. -/
theorem absDiff_self (a : ℝ≥0∞) : absDiff a a = 0 := by
  simp [absDiff, tsub_self]

/-- `absDiff` is symmetric. -/
theorem absDiff_comm (a b : ℝ≥0∞) : absDiff a b = absDiff b a := by
  simp [absDiff, max_comm]

/-- Triangle inequality for `absDiff`. -/
theorem absDiff_triangle (a b c : ℝ≥0∞) :
    absDiff a c ≤ absDiff a b + absDiff b c := by
  simp only [absDiff]
  apply max_le
  · calc a - c ≤ (a - b) + (b - c) := tsub_le_tsub_add_tsub
      _ ≤ ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc c - a ≤ (c - b) + (b - a) := tsub_le_tsub_add_tsub
      _ ≤ ((c - b) ⊔ (b - c)) + ((b - a) ⊔ (a - b)) :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
      _ = ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) := by
        rw [max_comm (c - b), max_comm (b - a), add_comm]

/-- If `f i ≤ g i + ε` for every `i` and the weights `w` sum to at most one,
then `∑' i, w i * f i ≤ ∑' i, w i * g i + ε`. -/
theorem weighted_bound {ι : Type} (w f g : ι → ℝ≥0∞) (ε : ℝ≥0∞)
    (hfg : ∀ i, f i ≤ g i + ε) (hw : ∑' i, w i ≤ 1) :
    ∑' i, w i * f i ≤ (∑' i, w i * g i) + ε := by
  calc ∑' i, w i * f i
      ≤ ∑' i, w i * (g i + ε) := by
        apply ENNReal.tsum_le_tsum; intro i; exact mul_le_mul_right (hfg i) _
    _ = ∑' i, (w i * g i + w i * ε) := by
        congr 1; funext i; exact mul_add (w i) (g i) ε
    _ = (∑' i, w i * g i) + ∑' i, w i * ε := ENNReal.tsum_add
    _ = (∑' i, w i * g i) + (∑' i, w i) * ε := by
        congr 1; exact ENNReal.tsum_mul_right
    _ ≤ (∑' i, w i * g i) + 1 * ε := by
        gcongr
    _ = (∑' i, w i * g i) + ε := by rw [one_mul]

/-- `absDiff a b ≤ ε` iff both `a ≤ b + ε` and `b ≤ a + ε`. -/
theorem absDiff_le_iff {a b ε : ℝ≥0∞} :
    absDiff a b ≤ ε ↔ (a ≤ b + ε ∧ b ≤ a + ε) := by
  constructor
  · intro h
    constructor
    · have : a - b ≤ ε := le_trans (le_max_left _ _) h
      calc a ≤ a - b + b := le_tsub_add
        _ ≤ ε + b := by gcongr
        _ = b + ε := add_comm _ _
    · have : b - a ≤ ε := le_trans (le_max_right _ _) h
      calc b ≤ b - a + a := le_tsub_add
        _ ≤ ε + a := by gcongr
        _ = a + ε := add_comm _ _
  · intro ⟨hab, hba⟩
    simp only [absDiff]
    apply max_le
    · exact tsub_le_iff_right.mpr (by rwa [add_comm])
    · exact tsub_le_iff_right.mpr (by rwa [add_comm])

/-- PSD matrix with zero trace is the zero matrix (wrapper for Mathlib). -/
private theorem psd_zero_of_trace_zero {M : Matrix d d ℂ}
    (hM : M.PosSemidef) (htr : M.trace = 0) : M = 0 :=
  hM.trace_eq_zero_iff.mp htr

/-- Imaginary part of the trace of a Hermitian matrix is zero. -/
theorem trace_im_zero_of_hermitian {M : Matrix d d ℂ}
    (hH : M.IsHermitian) : M.trace.im = 0 := by
  simpa [Matrix.trace] using
    Finset.sum_eq_zero fun i _ => Complex.conj_eq_iff_im.mp (congr_fun (congr_fun hH i) i)

/-- Weighted average bound for prTrue_Q under qbind.
    The core technical lemma: post-composition with ε-close continuations
    preserves the ε bound on prTrue_Q, for any shared prefix `c`. -/
theorem absDiff_prTrue_Q_qbind_le {α : Type} (c : QComp d α)
    (k₁ k₂ : α → QComp d Bool)
    (ρ : DensityMatrix d) (ε : ℝ≥0∞)
    (hk : ∀ a (ρ' : DensityMatrix d),
      absDiff (prTrue_Q (k₁ a) ρ') (prTrue_Q (k₂ a) ρ') ≤ ε) :
    absDiff (prTrue_Q (QComp.qbind c k₁) ρ)
            (prTrue_Q (QComp.qbind c k₂) ρ) ≤ ε := by
  -- Summability facts
  have hsum₁ : Summable (fun a => (k₁ a).branch true (c.branch a ρ.val)) :=
    QComp.bind_summable c k₁ true ρ.val
  have hsum₂ : Summable (fun a => (k₂ a).branch true (c.branch a ρ.val)) :=
    QComp.bind_summable c k₂ true ρ.val
  -- Unfold prTrue_Q of qbind to tsum of component traces
  have eq₁ : prTrue_Q (QComp.qbind c k₁) ρ =
      ENNReal.ofReal (∑' a, ((k₁ a).branch true (c.branch a ρ.val)).trace.re) := by
    simp only [prTrue_Q, QComp.qbind, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1; rw [trace_tsum hsum₁, Complex.re_tsum (trace_summable hsum₁)]
  have eq₂ : prTrue_Q (QComp.qbind c k₂) ρ =
      ENNReal.ofReal (∑' a, ((k₂ a).branch true (c.branch a ρ.val)).trace.re) := by
    simp only [prTrue_Q, QComp.qbind, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1; rw [trace_tsum hsum₂, Complex.re_tsum (trace_summable hsum₂)]
  rw [eq₁, eq₂]
  -- Each intermediate state c.branch a ρ.val is PSD
  have hσ_psd : ∀ a, (c.branch a ρ.val).PosSemidef :=
    fun a => c.branch_psd a ρ.val ρ.psd
  -- Each term is non-negative
  have hnn₁ : ∀ a, 0 ≤ ((k₁ a).branch true (c.branch a ρ.val)).trace.re :=
    fun a => trace_re_nonneg_of_psd ((k₁ a).branch_psd true _ (hσ_psd a))
  have hnn₂ : ∀ a, 0 ≤ ((k₂ a).branch true (c.branch a ρ.val)).trace.re :=
    fun a => trace_re_nonneg_of_psd ((k₂ a).branch_psd true _ (hσ_psd a))
  -- Convert to ENNReal tsum
  rw [ENNReal.ofReal_tsum_of_nonneg hnn₁ (trace_re_summable hsum₁),
      ENNReal.ofReal_tsum_of_nonneg hnn₂ (trace_re_summable hsum₂)]
  -- Suffices to show both ≤ directions
  rw [absDiff_le_iff]
  -- Weight function: w(a) = ofReal(trace(c.branch a ρ.val).re)
  -- Weights sum to ≤ 1 (from sub-TP of c and trace(ρ) = 1)
  have hw_sum : ∑' a, ENNReal.ofReal (c.branch a ρ.val).trace.re ≤ 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun a => trace_re_nonneg_of_psd (hσ_psd a))
      (trace_re_summable (c.branch_summable ρ.val))]
    calc ENNReal.ofReal (∑' a, (c.branch a ρ.val).trace.re)
        = ENNReal.ofReal (∑' a, (c.branch a ρ.val).trace).re := by
          congr 1; exact (Complex.re_tsum (trace_summable (c.branch_summable ρ.val))).symm
      _ ≤ ENNReal.ofReal ρ.val.trace.re :=
          ENNReal.ofReal_le_ofReal (c.branch_stp ρ.val ρ.psd)
      _ = 1 := by rw [ρ.tr_one]; simp
  -- Per-component bound: for each a, need both directions with weight w(a) * ε
  have hcomp : ∀ a,
      ENNReal.ofReal ((k₁ a).branch true (c.branch a ρ.val)).trace.re ≤
      ENNReal.ofReal ((k₂ a).branch true (c.branch a ρ.val)).trace.re +
        ENNReal.ofReal (c.branch a ρ.val).trace.re * ε ∧
      ENNReal.ofReal ((k₂ a).branch true (c.branch a ρ.val)).trace.re ≤
      ENNReal.ofReal ((k₁ a).branch true (c.branch a ρ.val)).trace.re +
        ENNReal.ofReal (c.branch a ρ.val).trace.re * ε := by
    intro a
    by_cases htr : (c.branch a ρ.val).trace = 0
    · -- Zero trace: c.branch a ρ.val = 0, all terms vanish
      have hzero : c.branch a ρ.val = 0 := psd_zero_of_trace_zero (hσ_psd a) htr
      simp [hzero, map_zero, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]
    · -- Non-zero trace: normalize to density matrix
      have him : (c.branch a ρ.val).trace.im = 0 :=
        trace_im_zero_of_hermitian (hσ_psd a).isHermitian
      have htr_re_pos : 0 < (c.branch a ρ.val).trace.re := by
        rcases lt_or_eq_of_le (trace_re_nonneg_of_psd (hσ_psd a)) with h | h
        · exact h
        · exact absurd (Complex.ext h.symm him) htr
      set t := (c.branch a ρ.val).trace.re
      have ht_ne : (↑t : ℂ) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr htr_re_pos.ne'
      -- Normalized matrix ρ'_val = (↑t⁻¹ : ℂ) • c.branch a ρ.val
      have hρ'_psd : ((↑t⁻¹ : ℂ) • c.branch a ρ.val).PosSemidef :=
        (hσ_psd a).smul (by
          rw [Complex.nonneg_iff]
          exact ⟨le_of_lt (inv_pos_of_pos htr_re_pos), by simp⟩)
      have htr_eq : (c.branch a ρ.val).trace = (↑t : ℂ) :=
        Complex.ext_iff.mpr ⟨rfl, by simpa using him⟩
      have hρ'_tr : ((↑t⁻¹ : ℂ) • c.branch a ρ.val).trace = 1 := by
        rw [Matrix.trace_smul, htr_eq,
          show (↑t⁻¹ : ℂ) = (↑t : ℂ)⁻¹ from by push_cast; ring]
        exact inv_mul_cancel₀ ht_ne
      set ρ' : DensityMatrix d :=
        ⟨(↑t⁻¹ : ℂ) • c.branch a ρ.val, hρ'_psd, hρ'_tr⟩
      -- Linearity: c.branch a ρ.val = (↑t : ℂ) • ρ'.val
      have hσ_eq : c.branch a ρ.val = (↑t : ℂ) • ρ'.val := by
        change c.branch a ρ.val = (↑t : ℂ) • ((↑t⁻¹ : ℂ) • c.branch a ρ.val)
        rw [smul_smul,
          show (↑t : ℂ) * (↑t⁻¹ : ℂ) = 1 from by
            rw [show (↑t⁻¹ : ℂ) = (↑t : ℂ)⁻¹ from by push_cast; ring]
            exact mul_inv_cancel₀ ht_ne]
        simp
      -- Scale factorization: (ki a).branch true (c.branch a ρ.val) = ↑t • (ki a).branch true ρ'.val
      -- This follows from hσ_eq and linearity of (ki a).branch true
      have hscale_mat : ∀ (ki : α → QComp d Bool),
          (ki a).branch true (c.branch a ρ.val) =
          (↑t : ℂ) • (ki a).branch true ρ'.val := by
        intro ki; rw [hσ_eq]; exact map_smul _ _ _
      have hscale : ∀ (ki : α → QComp d Bool),
          ((ki a).branch true (c.branch a ρ.val)).trace.re =
          t * ((ki a).branch true ρ'.val).trace.re := by
        intro ki
        rw [hscale_mat ki, Matrix.trace_smul]
        simp
      -- Apply hk to the normalized state
      have hk_a := absDiff_le_iff.mp (hk a ρ')
      -- Unfold prTrue_Q in hk_a to get ENNReal.ofReal form
      change ENNReal.ofReal ((k₁ a).branch true ρ'.val).trace.re ≤
          ENNReal.ofReal ((k₂ a).branch true ρ'.val).trace.re + ε ∧
        ENNReal.ofReal ((k₂ a).branch true ρ'.val).trace.re ≤
          ENNReal.ofReal ((k₁ a).branch true ρ'.val).trace.re + ε at hk_a
      constructor
      · rw [hscale k₁, hscale k₂,
            ENNReal.ofReal_mul (le_of_lt htr_re_pos),
            ENNReal.ofReal_mul (le_of_lt htr_re_pos), ← mul_add]
        exact mul_le_mul_right hk_a.1 _
      · rw [hscale k₁, hscale k₂,
            ENNReal.ofReal_mul (le_of_lt htr_re_pos),
            ENNReal.ofReal_mul (le_of_lt htr_re_pos), ← mul_add]
        exact mul_le_mul_right hk_a.2 _
  -- Assemble: ∑ f ≤ ∑ g + ε (both directions) using weighted sum bound
  have assemble : ∀ (f g : α → ℝ≥0∞),
      (∀ a, f a ≤ g a + ENNReal.ofReal (c.branch a ρ.val).trace.re * ε) →
      (∑' a, f a ≤ (∑' a, g a) + ε) := by
    intro f g hfg
    calc ∑' a, f a
        ≤ ∑' a, (g a + ENNReal.ofReal (c.branch a ρ.val).trace.re * ε) :=
          ENNReal.tsum_le_tsum hfg
      _ = (∑' a, g a) + ∑' a, ENNReal.ofReal (c.branch a ρ.val).trace.re * ε :=
          ENNReal.tsum_add
      _ = (∑' a, g a) + (∑' a, ENNReal.ofReal (c.branch a ρ.val).trace.re) * ε := by
          congr 1; exact ENNReal.tsum_mul_right
      _ ≤ (∑' a, g a) + 1 * ε := by gcongr
      _ = (∑' a, g a) + ε := by rw [one_mul]
  exact ⟨assemble _ _ (fun a => (hcomp a).1), assemble _ _ (fun a => (hcomp a).2)⟩

end Quantum
