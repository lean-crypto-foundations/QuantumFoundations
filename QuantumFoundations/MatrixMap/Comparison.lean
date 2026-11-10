/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.MatrixMap.Kraus
public import QuantumFoundations.MatrixMap.Norm

/-!
# Comparing Kraus operators under a finishing map

A completely positive trace-nonincreasing finishing map preserves the square-root triangle
inequality for the Kraus operators applied before it. Consequently, replacing the preceding
operators costs at most the square root of their difference weight, a finishing map that
vanishes on a subspace is bounded by its weight on the complement, and two measured
replacements around a trace-nonincreasing family add their operator-norm distances.
-/

public section

open Matrix
open scoped ComplexOrder ENNReal Matrix.Norms.L2Operator

namespace Quantum.MatrixMap

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- A completely positive trace-nonincreasing finishing map preserves the square-root triangle
inequality for two preceding Kraus operators. -/
theorem IsCP.finish_triangle {Φ : MatrixMap B C} (hΦ : Φ.IsCP) (hT : Φ.IsTNI)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) (K L : Matrix B A ℂ) :
    ENNReal.ofReal (Φ (conj (K + L) ρ)).trace.re ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (Φ (conj K ρ)).trace.re ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (Φ (conj L ρ)).trace.re ^ (2⁻¹ : ℝ) := by
  classical
  obtain ⟨S, rfl, _⟩ := hΦ.exists_stinespring_of_isTNI hT
  simp only [LinearMap.comp_apply, trace_traceRight]
  simp only [← LinearMap.comp_apply, ← conj_mul]
  rw [Matrix.mul_add]
  exact ofReal_trace_conj_add_rpow_le hρ _ _

/-- Replacing preceding Kraus operators adds their difference before taking the final square.
The finishing map can depend on the measured classical outcome. -/
theorem finish_comparison {ι : Type*} (Φ : ι → MatrixMap B C)
    (hΦ : ∀ i, (Φ i).IsCP) (hT : ∀ i, (Φ i).IsTNI)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) (K L : ι → Matrix B A ℂ) :
    (∑' i, ENNReal.ofReal (Φ i (conj (K i) ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' i, ENNReal.ofReal (Φ i (conj (L i) ρ)).trace.re) ^ (2⁻¹ : ℝ) +
        (∑' i, ENNReal.ofReal (conj (K i - L i) ρ).trace.re) ^ (2⁻¹ : ℝ) := by
  apply rpow_inv_two_tsum_le_of_le_add
  intro i
  have hh := (hΦ i).finish_triangle (hT i) hρ (L i) (K i - L i)
  rw [show L i + (K i - L i) = K i by abel] at hh
  apply hh.trans
  apply add_le_add le_rfl
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
    (hT i _ ((isCP_conj (K i - L i)).posSemidef hρ))) (by norm_num)

/-- A finishing branch that vanishes on a subspace is bounded by its action on the
complement. This retains coherent cross terms until the square-root triangle inequality. -/
theorem IsCP.finish_le_complement [DecidableEq A] {Φ : MatrixMap B C}
    (hΦ : Φ.IsCP) (hT : Φ.IsTNI) (K : Matrix B A ℂ) (G : Matrix A A ℂ)
    (hzero : Φ ∘ₗ conj (K * G) = 0) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ENNReal.ofReal (Φ (conj K ρ)).trace.re ≤
      ENNReal.ofReal (Φ (conj K (conj (1 - G) ρ))).trace.re := by
  have h := hΦ.finish_triangle hT hρ (K * (1 - G)) (K * G)
  have he : K * (1 - G) + K * G = K := by
    simp only [Matrix.mul_sub, Matrix.mul_one, sub_add_cancel]
  rw [he] at h
  have hz := LinearMap.congr_fun hzero ρ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  rw [hz, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), add_zero] at h
  rw [conj_mul, LinearMap.comp_apply] at h
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2⁻¹)).mp h

/-- An outcome-dependent family of finishing branches that all vanish after `G` has total weight
at most the weight of the input on the complement, `tr ((1 - G) ρ (1 - G)ᴴ)`. -/
theorem finish_sum_le_complement [DecidableEq A] {ι : Type*}
    (Φ : ι → MatrixMap B C) (hΦ : ∀ i, (Φ i).IsCP) (hT : ∀ i, (Φ i).IsTNI)
    (K : ι → Matrix B A ℂ) (hK : IsCPTNIFamily (fun i ↦ conj (K i)))
    (G : Matrix A A ℂ) (hzero : ∀ i, Φ i ∘ₗ conj (K i * G) = 0)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ∑' i, ENNReal.ofReal (Φ i (conj (K i) ρ)).trace.re ≤
      ENNReal.ofReal (conj (1 - G) ρ).trace.re := by
  calc _ ≤ ∑' i, ENNReal.ofReal (Φ i (conj (K i) (conj (1 - G) ρ))).trace.re :=
          ENNReal.tsum_le_tsum fun i ↦ (hΦ i).finish_le_complement
            (hT i) (K i) G (hzero i) hρ
    _ ≤ ∑' i, ENNReal.ofReal (conj (K i) (conj (1 - G) ρ)).trace.re := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact ENNReal.ofReal_le_ofReal
        (hT i _ ((isCP_conj _).posSemidef ((isCP_conj _).posSemidef hρ)))
    _ ≤ _ := hK.tsum_ofReal_trace_re_le ((isCP_conj _).posSemidef hρ)

/-- A classical predicate followed by a label measurement is a trace-nonincreasing family. -/
theorem accepted_label_isCPTNIFamily [DecidableEq A] {ι : Type*}
    [DecidableEq ι] (p : A → Prop) [DecidablePred p] (β : A → ι) :
    IsCPTNIFamily (fun i ↦ conj (diagonal fun a ↦
      if p a ∧ β a = i then (1 : ℂ) else 0)) := by
  classical
  let K (i : ι) : Matrix A A ℂ := diagonal fun a ↦ if p a ∧ β a = i then 1 else 0
  refine ⟨fun _ ↦ isCP_conj _, fun s ρ hρ ↦ ?_⟩
  have hg : ∑ i ∈ s, (K i)ᴴ * K i =
      diagonal (fun a ↦ if p a ∧ β a ∈ s then (1 : ℂ) else 0) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp only [K, Matrix.sum_apply, diagonal_conjTranspose, diagonal_mul_diagonal,
        diagonal_apply_eq]
      by_cases hp : p a <;> simp [hp]
    · simp [K, Matrix.sum_apply, diagonal_conjTranspose, diagonal_mul_diagonal, hab]
  have ht : (1 - ∑ i ∈ s, (K i)ᴴ * K i).PosSemidef := by
    rw [hg, ← diagonal_one, diagonal_sub]
    apply PosSemidef.diagonal
    intro a
    by_cases hp : p a ∧ β a ∈ s <;> simp [hp]
  have hh := ht.trace_mul_re_nonneg hρ
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    Finset.sum_mul, Matrix.trace_sum, Complex.re_sum, ← trace_conj_apply] at hh
  exact sub_nonneg.mp hh

/-- Operator norm bounds for a family measured between two operators. The middle family's
trace bound is used once, so the estimate does not multiply by its number of outcomes. -/
theorem measured_sandwich_weight_le [DecidableEq A] {ι : Type*}
    (P : ι → Matrix A A ℂ) (hP : IsCPTNIFamily (fun i ↦ conj (P i)))
    (L R : Matrix A A ℂ) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    (∑' i, ENNReal.ofReal (conj (L * P i * R) ρ).trace.re) ≤
      ENNReal.ofReal (‖L‖ ^ 2) * ENNReal.ofReal (conj R ρ).trace.re := by
  calc _ ≤ ∑' i, ENNReal.ofReal (‖L‖ ^ 2) *
      ENNReal.ofReal (conj (P i) (conj R ρ)).trace.re := by
        apply ENNReal.tsum_le_tsum
        intro i
        rw [Matrix.mul_assoc, conj_mul, LinearMap.comp_apply, conj_mul,
          LinearMap.comp_apply, ← ENNReal.ofReal_mul (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (re_trace_conj_le L
          ((isCP_conj _).posSemidef ((isCP_conj _).posSemidef hρ)))
    _ = ENNReal.ofReal (‖L‖ ^ 2) *
        ∑' i, ENNReal.ofReal (conj (P i) (conj R ρ)).trace.re := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul_right (hP.tsum_ofReal_trace_re_le ((isCP_conj _).posSemidef hρ)) _

/-- Two replacements, `Pa` by `Qa` before a trace-nonincreasing family and `Pb` by `Qb` after
it, are compared while every intermediate measurement outcome is retained. Their amplitudes add,
and the bound keeps the input trace so that it can be summed over further outcomes. -/
theorem measured_two_batches_distance_le [DecidableEq A] {ι : Type*}
    (P : ι → Matrix A A ℂ) (hP : IsCPTNIFamily (fun i ↦ conj (P i)))
    (Qa Qb Pa Pb : Matrix A A ℂ) (hQb : ‖Qb‖ ≤ 1) (hPa : ‖Pa‖ ≤ 1)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    (∑' i, ENNReal.ofReal (conj (Qb * P i * Qa - Pb * P i * Pa) ρ).trace.re) ^
        (2⁻¹ : ℝ) ≤
      (ENNReal.ofReal (‖Qa - Pa‖ ^ 2) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (‖Qb - Pb‖ ^ 2) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  have htrace (M : Matrix A A ℂ) : ENNReal.ofReal (conj M ρ).trace.re ≤
      ENNReal.ofReal (‖M‖ ^ 2) * ENNReal.ofReal ρ.trace.re := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (re_trace_conj_le M hρ)
  have hsq {M : Matrix A A ℂ} (hM : ‖M‖ ≤ 1) : ENNReal.ofReal (‖M‖ ^ 2) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    nlinarith [norm_nonneg M]
  have htriangle := rpow_inv_two_tsum_le_of_le_add (t := fun i ↦
    ENNReal.ofReal (conj (Qb * P i * Qa - Pb * P i * Pa) ρ).trace.re)
    (a := fun i ↦ ENNReal.ofReal (conj (Qb * P i * (Qa - Pa)) ρ).trace.re)
    (b := fun i ↦ ENNReal.ofReal (conj ((Qb - Pb) * P i * Pa) ρ).trace.re) (fun i ↦ ?_)
  · apply htriangle.trans
    apply add_le_add <;> apply ENNReal.rpow_le_rpow _ (by norm_num)
    · exact (measured_sandwich_weight_le P hP Qb (Qa - Pa) hρ).trans
        ((mul_le_of_le_one_left (by positivity) (hsq hQb)).trans (htrace _))
    · exact (measured_sandwich_weight_le P hP (Qb - Pb) Pa hρ).trans
        (mul_le_mul_right ((htrace Pa).trans
          (mul_le_of_le_one_left (by positivity) (hsq hPa))) _)
  · have he : Qb * P i * Qa - Pb * P i * Pa =
        Qb * P i * (Qa - Pa) + (Qb - Pb) * P i * Pa := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [he]
    exact ofReal_trace_conj_add_rpow_le hρ _ _

end Quantum.MatrixMap

namespace Quantum.MatrixMap

/-- The sum of the trace weights of the differences of two complete Kraus families is at most
four times the input trace. -/
theorem sum_trace_conj_sub_le_four {n m ι : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [Fintype ι] (F G : ι → Matrix m n ℂ)
    (hF : ∑ a, (F a)ᴴ * F a = 1) (hG : ∑ a, (G a)ᴴ * G a = 1)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    ∑ a, ENNReal.ofReal (MatrixMap.conj (F a - G a) ρ).trace.re ≤
      4 * ENNReal.ofReal ρ.trace.re := by
  have hpoint (a : ι) : (MatrixMap.conj (F a - G a) ρ).trace.re ≤
      2 * ((MatrixMap.conj (F a) ρ).trace.re + (MatrixMap.conj (G a) ρ).trace.re) := by
    have hp := (hρ.mul_mul_conjTranspose_same (F a + G a)).trace_re_nonneg
    have he : MatrixMap.conj (F a - G a) ρ + MatrixMap.conj (F a + G a) ρ =
        (MatrixMap.conj (F a) ρ + MatrixMap.conj (G a) ρ) +
        (MatrixMap.conj (F a) ρ + MatrixMap.conj (G a) ρ) := by
      simp only [MatrixMap.conj_apply, conjTranspose_sub, conjTranspose_add]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add]
      abel
    have ht := congrArg (fun M ↦ M.trace.re) he
    simp only [trace_add, Complex.add_re] at ht
    have hp' : 0 ≤ (MatrixMap.conj (F a + G a) ρ).trace.re := hp
    linarith
  have hf := congrArg Complex.re (MatrixMap.isTP_sum_conj hF ρ)
  have hg := congrArg Complex.re (MatrixMap.isTP_sum_conj hG ρ)
  simp only [LinearMap.sum_apply, trace_sum, Complex.re_sum] at hf hg
  have hn (a : ι) : 0 ≤ (MatrixMap.conj (F a - G a) ρ).trace.re :=
    (hρ.mul_mul_conjTranspose_same (F a - G a)).trace_re_nonneg
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ hn a),
    ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ a, 2 * ((MatrixMap.conj (F a) ρ).trace.re +
        (MatrixMap.conj (G a) ρ).trace.re) := Finset.sum_le_sum fun a _ ↦ hpoint a
    _ = 4 * ρ.trace.re := by rw [← Finset.mul_sum, Finset.sum_add_distrib, hf, hg]; ring

/-- Domination of a Kraus operator's Gram matrix bounds its trace weight by the same trace
pairing on every positive semidefinite input. -/
theorem ofReal_trace_conj_le {J O : Type*} [Fintype J] [Fintype O]
    (C : Matrix O J ℂ) (Δ : Matrix J J ℂ) {r : ℝ} (hr : 0 ≤ r)
    (h : (r • Δ - Cᴴ * C).PosSemidef) {σ : Matrix J J ℂ} (hσ : σ.PosSemidef) :
    ENNReal.ofReal (MatrixMap.conj C σ).trace.re ≤
      ENNReal.ofReal r * ENNReal.ofReal (Δ * σ).trace.re := by
  have ht := h.trace_mul_re_nonneg hσ
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.real_smul, Complex.re_ofReal_mul] at ht
  rw [← ENNReal.ofReal_mul hr, MatrixMap.trace_conj_apply]
  exact ENNReal.ofReal_le_ofReal (sub_nonneg.mp ht)

/-- A finite Kraus family dominated by two weighted operators has trace weight bounded by the
same weighted trace pairings on every positive semidefinite input. -/
theorem tsum_ofReal_trace_conj_le_of_posSemidef {J O ι : Type*} [Fintype J] [Fintype O]
    [Fintype ι] (C : ι → Matrix O J ℂ) (Δ Ε : Matrix J J ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {σ : Matrix J J ℂ} (hσ : σ.PosSemidef)
    (hC : (a • Δ + b • Ε - ∑ r, (C r)ᴴ * C r).PosSemidef) :
    ∑' r, ENNReal.ofReal (conj (C r) σ).trace.re ≤
      ENNReal.ofReal a * ENNReal.ofReal (Δ * σ).trace.re +
        ENNReal.ofReal b * ENNReal.ofReal (Ε * σ).trace.re := by
  have hnn : ∀ r, 0 ≤ (conj (C r) σ).trace.re := fun r ↦
    (hσ.mul_mul_conjTranspose_same _).trace_re_nonneg
  have hpos := hC.trace_mul_re_nonneg hσ
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, Complex.sub_re, Complex.add_re,
    Complex.re_sum, Complex.real_smul, Complex.re_ofReal_mul] at hpos
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hnn r,
    ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  simp only [trace_conj_apply]
  linarith

end Quantum.MatrixMap
