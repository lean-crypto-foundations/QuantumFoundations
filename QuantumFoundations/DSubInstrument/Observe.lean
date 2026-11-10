/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.Oracle.Basis
public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Outcome measures of subinstruments

Outcome measures respect equal branch traces, framing and measurable changes of outcomes.
Lossless continuations preserve the marginal distribution of earlier outcomes.
-/

public section

open Matrix
open MeasureTheory
open scoped ComplexOrder ENNReal

namespace Quantum

namespace DSubInstrument

variable {X X' : Type*} [Fintype X] [Fintype X'] {ι κ : Type*} {B B' : ι → Type*}
  [∀ i, Fintype (B i)] [∀ i, Fintype (B' i)] {C C' : κ → Type*} [∀ c, Fintype (C c)]
  [∀ c, Fintype (C' c)]

/-- On the zero substate every outcome has weight zero. -/
theorem outcomeMeasure_eq_zero_of_matrix_eq_zero [MeasurableSpace ι] (p : DSubInstrument X ι B)
    {ρ : SubState X} (hρ : ρ.matrix = 0) : p.outcomeMeasure ρ = 0 := by
  ext s hs
  simp [outcomeMeasure_apply _ _ hs, hρ]

/-- Two dependent subinstruments whose branches leave operators of the same trace on two
substates, on every outcome, have the same outcome measures on them. -/
theorem outcomeMeasure_congr [MeasurableSpace ι] {p : DSubInstrument X ι B}
    {p' : DSubInstrument X' ι B'} {ρ : SubState X} {ρ' : SubState X'}
    (h : ∀ i, (p.branch i ρ.matrix).trace = (p'.branch i ρ'.matrix).trace) :
    p.outcomeMeasure ρ = p'.outcomeMeasure ρ' := by
  rw [outcomeMeasure_eq_sum, outcomeMeasure_eq_sum]
  exact congrArg Measure.sum <| funext fun i ↦ by rw [h i]

end DSubInstrument

namespace DSubInstrument

/-- Framing does not change the outcome distribution, which depends only on the reduced input
state. -/
theorem outcomeMeasure_frame {A ι : Type*} [Fintype A] [MeasurableSpace ι] {B : ι → Type*}
    [∀ i, Fintype (B i)] (p : DSubInstrument A ι B) (R : Type*) [Fintype R]
    (σ : SubState (A × R)) :
    (p.frame R).outcomeMeasure σ = p.outcomeMeasure σ.traceRight := by
  simp only [outcomeMeasure_eq_sum, branch_frame_apply, MatrixMap.trace_amplify_apply,
    SubState.matrix_traceRight, MatrixMap.traceRight_eq_sum_submatrix, map_sum, Matrix.trace_sum]

end DSubInstrument

namespace SubInstrument

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {α β : Type*}

/-- Relabelling the outcomes of a subinstrument along a measurable map pushes its outcome
measure forward along the map. -/
theorem outcomeMeasure_map_eq_map [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (p : SubInstrument A B α) (ρ : SubState A) :
    (p.map f).outcomeMeasure ρ = (p.outcomeMeasure ρ).map f := by
  rw [DSubInstrument.outcomeMeasure_map, DSubInstrument.outcomeMeasure_eq_sum,
    Measure.map_sum hf.aemeasurable]
  refine congrArg Measure.sum (funext fun a ↦ ?_)
  rw [Measure.map_smul, Measure.map_dirac' hf]
  exact hf.aemeasurable

/-- Tagging every outcome of a lossless subinstrument with `a` and forgetting the outcome leaves
the point mass at `a` with the weight of the input. -/
theorem map_fst_outcomeMeasure_map_prodMk [MeasurableSpace α] [MeasurableSpace β]
    {p : SubInstrument A B β} (hp : p.Lossless) (a : α) (ρ : SubState A) :
    ((p.map (Prod.mk a)).outcomeMeasure ρ).map Prod.fst =
      ENNReal.ofReal ρ.matrix.trace.re • Measure.dirac a := by
  rw [outcomeMeasure_map_eq_map measurable_prodMk_left,
    Measure.map_map measurable_fst measurable_prodMk_left,
    show (Prod.fst ∘ Prod.mk a : β → α) = fun _ ↦ a from rfl, Measure.map_const,
    hp.outcomeMeasure_apply_univ]

/-- If after each outcome `a` of `p` a lossless subinstrument `k a` is run and `a` is reported
together with its outcome, the first component of the joint outcome has the law of `p`. -/
theorem map_fst_outcomeMeasure_bind_map_prodMk [MeasurableSpace α] [MeasurableSpace β]
    (p : SubInstrument A B α) {k : α → SubInstrument B C β} (hk : ∀ a, (k a).Lossless)
    (ρ : SubState A) :
    ((p.bind fun a ↦ (k a).map (Prod.mk a)).outcomeMeasure ρ).map Prod.fst =
      p.outcomeMeasure ρ := by
  rw [DSubInstrument.outcomeMeasure_bind, Measure.map_sum measurable_fst.aemeasurable,
    DSubInstrument.outcomeMeasure_eq_sum]
  refine congrArg Measure.sum (funext fun a ↦ ?_)
  rw [map_fst_outcomeMeasure_map_prodMk (hk a), DSubInstrument.matrix_post]

end SubInstrument

/-- **A uniform bound through a composite.** If, after every outcome `a` of `p`, the continuation
`k a` puts weight at most `ε` times the trace of the post-branch substate on `s`, then the
composite puts weight at most `ε` times the trace of the input on `s`. -/
theorem SubInstrument.outcomeMeasure_bind_le {A B C : Type*} [Fintype A] [Fintype B]
    [Fintype C] {α β : Type*} [MeasurableSpace β] (p : SubInstrument A B α)
    (k : α → SubInstrument B C β) (ρ : SubState A) {s : Set β} (hs : MeasurableSet s)
    {ε : ℝ≥0∞}
    (h : ∀ a, (k a).outcomeMeasure (p.post ρ a) s ≤
      ε * ENNReal.ofReal (p.branch a ρ.matrix).trace.re) :
    (p.bind k).outcomeMeasure ρ s ≤ ε * ENNReal.ofReal ρ.matrix.trace.re := by
  let _ : MeasurableSpace α := ⊤
  rw [DSubInstrument.outcomeMeasure_bind, Measure.sum_apply _ hs]
  calc ∑' a, (k a).outcomeMeasure (p.post ρ a) s
      ≤ ∑' a, ε * ENNReal.ofReal (p.branch a ρ.matrix).trace.re := ENNReal.tsum_le_tsum h
    _ = ε * p.outcomeMeasure ρ Set.univ := by
        rw [ENNReal.tsum_mul_left, DSubInstrument.outcomeMeasure_apply _ _ MeasurableSet.univ]
        simp
    _ ≤ ε * ENNReal.ofReal ρ.matrix.trace.re := by
        rw [SubInstrument.outcomeMeasure_apply_univ]
        exact mul_le_mul_of_nonneg_left
          (ENNReal.ofReal_le_ofReal (p.isTNI_total _ ρ.posSemidef)) zero_le

end Quantum
