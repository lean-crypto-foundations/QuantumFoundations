/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.Bridge.ToQComp
public import QuantumFoundations.Measurement
public import QuantumFoundations.UnitaryChannel
public import QuantumFoundations.InstrumentCP
public import QuantumFoundations.SubInstrument
public import QuantumFoundations.Observe
public import QuantumFoundations.Pure.Instrument

/-!
# Agreement of the two developments of states and instruments

The repository contains two developments of quantum states and instruments, both in namespace
`Quantum`:

* `Quantum.DensityMatrix` and `Quantum.QComp`, with positive branches on `Matrix d d ℂ`, a
  summability field and a bound on the trace of the sum;
* `Quantum.SubState` and `Quantum.SubInstrument A B α`, with completely positive branches
  (`Quantum.MatrixMap.IsCP`) from `A` to `B` and a bound on every finite partial sum of traces.

This file proves that the overlapping definitions agree.

## The pairs

* **States.** A `DensityMatrix d` is a `SubState d` of trace one (`DensityMatrix.toSubState`,
  injective, with inverse `DensityMatrix.ofSubState` on trace-one substates).
* **Instruments.** A `SubInstrument d d α` is a `QComp d α` (`SubInstrument.toQComp`, defined
  in `QuantumFoundations.Bridge.ToQComp`), and the map is injective. Its image is the set of
  `QComp`s whose branches are completely positive (`QComp.toSubInstrument`,
  `SubInstrument.equivCP`). The map is not onto: a `QComp` admits positive branches that are
  not completely positive, such as the transpose map.
* **Monad structure.** `SubInstrument.toQComp` commutes with `pure`, `bind`, `map` and failure,
  so it is a monad morphism `SubInstrument d d ⟶ QComp d`.
* **Observation.** `prTrue_Q` of the image of `p` is the outcome measure of `p` at `{true}`.
* **Measurements.** `QComp.ofKraus`, `Measurement.measureOps`,
  `Measurement.projectiveMeasure`, `measureProj` and `UnitaryChannel.unitaryChannel` are
  defined as images of `SubInstrument.ofKraus`. The projective ones are the images of
  `SubInstrument.ofProjective`, and the unitary channel is the image of
  `SubInstrument.ofUnitary`. The effects `Mᴴ M` of measurement operators form a POVM
  (`Measurement.MeasurementOps.toPOVM`) whose Born probabilities are the outcome weights of the
  Kraus subinstrument.

## Main results

* `Quantum.DensityMatrix.toSubState_injective`
* `Quantum.SubInstrument.toQComp_injective`, `Quantum.SubInstrument.equivCP`
* `Quantum.SubInstrument.toQComp_pure`, `Quantum.SubInstrument.toQComp_bind`,
  `Quantum.SubInstrument.toQComp_map`, `Quantum.SubInstrument.toQComp_fail`
* `Quantum.SubInstrument.prTrue_Q_toQComp`
* `Quantum.Measurement.projectiveMeasure_eq_toQComp`, `Quantum.measureProj_eq_toQComp`,
  `Quantum.UnitaryChannel.unitaryChannel_eq_toQComp`
* `Quantum.Measurement.outcomeMeasure_ofKraus_singleton`
-/

@[expose] public section

open scoped Matrix ComplexOrder ENNReal
open Matrix

noncomputable section

namespace Quantum

variable {d : Type*} [Fintype d] {α β : Type}

/-! ## States -/

namespace DensityMatrix

/-- A density matrix as a substate of trace one. -/
def toSubState (ρ : DensityMatrix d) : SubState d where
  matrix := ρ.val
  posSemidef := ρ.psd
  trace_re_le_one := by rw [ρ.tr_one, Complex.one_re]

/-- The matrix of `ρ.toSubState` is the matrix of `ρ`. -/
@[simp]
theorem matrix_toSubState (ρ : DensityMatrix d) : ρ.toSubState.matrix = ρ.val :=
  rfl

/-- Distinct density matrices are distinct substates. -/
theorem toSubState_injective : Function.Injective (toSubState (d := d)) := by
  rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
  cases congrArg SubState.matrix h
  rfl

/-- A substate of trace one as a density matrix. -/
def ofSubState (ρ : SubState d) (h : ρ.matrix.trace = 1) : DensityMatrix d where
  val := ρ.matrix
  psd := ρ.posSemidef
  tr_one := h

/-- `ofSubState` followed by `toSubState` is the identity. -/
@[simp]
theorem toSubState_ofSubState (ρ : SubState d) (h : ρ.matrix.trace = 1) :
    (ofSubState ρ h).toSubState = ρ :=
  rfl

/-- `toSubState` followed by `ofSubState` is the identity. -/
@[simp]
theorem ofSubState_toSubState (ρ : DensityMatrix d) :
    ofSubState ρ.toSubState ρ.tr_one = ρ :=
  rfl

end DensityMatrix

/-! ## Instruments -/

namespace SubInstrument

/-- Distinct subinstruments are distinct positive instruments. -/
theorem toQComp_injective : Function.Injective (toQComp (d := d) (α := α)) :=
  fun _ _ h ↦ DSubInstrument.ext (congrArg QComp.branch h)

/-- Every branch of the image of a subinstrument is completely positive. -/
theorem isCP_toQComp_branch (p : SubInstrument d d α) (a : α) :
    MatrixMap.IsCP (p.toQComp.branch a) :=
  p.isCP_branch a

end SubInstrument

namespace QComp

/-- A positive instrument whose branches are completely positive as a subinstrument. -/
def toSubInstrument (I : QComp d α) (h : ∀ a, MatrixMap.IsCP (I.branch a)) :
    SubInstrument d d α where
  branch := I.branch
  isCP_branch := h
  trace_le s ρ hρ := by
    have hs := trace_re_summable (I.branch_summable ρ)
    calc ∑ a ∈ s, (I.branch a ρ).trace.re
        ≤ ∑' a, (I.branch a ρ).trace.re :=
          hs.sum_le_tsum s fun a _ ↦ trace_re_nonneg_of_psd (I.branch_psd a ρ hρ)
      _ = (∑' a, (I.branch a ρ).trace).re :=
          (Complex.re_tsum (trace_summable (I.branch_summable ρ))).symm
      _ ≤ ρ.trace.re := I.branch_stp ρ hρ

/-- The branches of `I.toSubInstrument h` are those of `I`. -/
@[simp]
theorem toSubInstrument_branch (I : QComp d α) (h : ∀ a, MatrixMap.IsCP (I.branch a)) :
    (I.toSubInstrument h).branch = I.branch :=
  rfl

/-- `toSubInstrument` followed by `toQComp` is the identity. -/
@[simp]
theorem toQComp_toSubInstrument (I : QComp d α) (h : ∀ a, MatrixMap.IsCP (I.branch a)) :
    (I.toSubInstrument h).toQComp = I :=
  QComp.ext fun _ ↦ rfl

end QComp

namespace SubInstrument

/-- `toQComp` followed by `toSubInstrument` is the identity. -/
@[simp]
theorem toSubInstrument_toQComp (p : SubInstrument d d α) :
    p.toQComp.toSubInstrument p.isCP_toQComp_branch = p :=
  DSubInstrument.ext rfl

/-- Subinstruments on `d` are the positive instruments on `d` whose branches are completely
positive. -/
def equivCP : SubInstrument d d α ≃ {I : QComp d α // ∀ a, MatrixMap.IsCP (I.branch a)} where
  toFun p := ⟨p.toQComp, p.isCP_toQComp_branch⟩
  invFun I := I.1.toSubInstrument I.2
  left_inv p := p.toSubInstrument_toQComp
  right_inv I := Subtype.ext (I.1.toQComp_toSubInstrument I.2)

/-! ## Monad structure -/

/-- `toQComp` preserves `pure`. -/
@[simp]
theorem toQComp_pure (a : α) : (pure a : SubInstrument d d α).toQComp = pure a := by
  refine QComp.ext fun a' ↦ ?_
  change (SubInstrument.pure a : SubInstrument d d α).branch a' = (QComp.qpure a).branch a'
  by_cases h : a' = a
  · subst h
    simp [QComp.qpure]
  · simp [QComp.qpure, h]

/-- `toQComp` preserves `bind`. -/
@[simp]
theorem toQComp_bind (p : SubInstrument d d α) (k : α → SubInstrument d d β) :
    (p >>= k).toQComp = p.toQComp >>= fun a ↦ (k a).toQComp :=
  QComp.ext_fun fun b ρ ↦ DSubInstrument.branch_bind_apply p k b ρ

/-- `toQComp` preserves `map`. -/
@[simp]
theorem toQComp_map (f : α → β) (p : SubInstrument d d α) :
    (f <$> p).toQComp = f <$> p.toQComp := by
  rw [map_eq_pure_bind, toQComp_bind, map_eq_pure_bind]
  simp only [toQComp_pure]

/-- `toQComp` sends the failing subinstrument to the failing instrument. -/
@[simp]
theorem toQComp_fail : (SubInstrument.fail : SubInstrument d d α).toQComp = QComp.qfail :=
  QComp.ext fun _ ↦ rfl

/-! ## Observation -/

/-- The probability of `true` under the image of a Boolean subinstrument is the weight of the
outcome `true` in its outcome measure. -/
theorem prTrue_Q_toQComp (p : SubInstrument d d Bool) (ρ : DensityMatrix d) :
    prTrue_Q p.toQComp ρ = p.outcomeMeasure ρ.toSubState {true} := by
  rw [DSubInstrument.outcomeMeasure_apply_singleton]
  rfl

end SubInstrument

/-! ## Measurements -/

namespace Measurement

variable [DecidableEq d]

/-- Every operator of a projective measurement is a star projection. -/
theorem ProjectiveMeasurement.isStarProjection [Fintype α] (P : ProjectiveMeasurement d α)
    (a : α) : IsStarProjection (P.op a) :=
  ⟨P.idempotent a, P.self_adjoint a⟩

/-- The operators of a projective measurement sum to the identity. -/
theorem ProjectiveMeasurement.sum_op [Fintype α] (P : ProjectiveMeasurement d α) :
    ∑ a, P.op a = 1 := by
  simpa only [P.self_adjoint, P.idempotent] using P.completeness

/-- The instrument of a projective measurement is the image of its projective subinstrument. -/
theorem projectiveMeasure_eq_toQComp [Fintype α] (P : ProjectiveMeasurement d α) :
    projectiveMeasure P =
      (SubInstrument.ofProjective P.op P.isStarProjection P.sum_op).toQComp :=
  QComp.ext_fun fun _ _ ↦ rfl

/-- The effects `Mᴴ M` of measurement operators form a POVM. -/
def MeasurementOps.toPOVM [Fintype α] (M : MeasurementOps d α) : POVM d α where
  effect a := (M.op a)ᴴ * M.op a
  effect_psd a := Matrix.posSemidef_conjTranspose_mul_self (M.op a)
  sum_eq_one := M.completeness

/-- The weight of outcome `a` of the Kraus subinstrument of measurement operators is the Born
probability of `a` under their POVM. -/
theorem outcomeMeasure_ofKraus_singleton [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (M : MeasurementOps d α) (ρ : SubState d) (a : α) :
    (SubInstrument.ofKraus M.op M.completeness).outcomeMeasure ρ {a} =
      ENNReal.ofReal (bornProb M.toPOVM ρ.matrix a).re := by
  rw [DSubInstrument.outcomeMeasure_apply_singleton]
  rw [bornProb, MeasurementOps.toPOVM, SubInstrument.ofKraus,
    DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply, Matrix.trace_mul_cycle]

end Measurement

open GentleMeasurement in
/-- The projective instrument `{P, 1 - P}` is the image of the projective subinstrument. -/
theorem measureProj_eq_toQComp [DecidableEq d] (P : Projector d) :
    measureProj P =
      (SubInstrument.ofProjective (fun b ↦ if b then P.val else 1 - P.val)
        (fun b ↦ by
          have hP : IsStarProjection P.val := ⟨P.idempotent, P.self_adjoint⟩
          cases b
          · exact hP.one_sub
          · exact hP)
        (by simp)).toQComp := by
  refine QComp.ext_fun fun b ρ ↦ ?_
  cases b
  · simp [measureProj_branch_false, P.self_adjoint]
  · simp [measureProj_branch_true, P.self_adjoint]

namespace UnitaryChannel

/-- The unitary channel of `U` is the image of the unitary subinstrument of `U`. -/
theorem unitaryChannel_eq_toQComp [DecidableEq d] (U : Matrix.unitaryGroup d ℂ) :
    unitaryChannel U = (SubInstrument.ofUnitary U).toQComp :=
  QComp.ext_fun fun _ _ ↦ rfl

end UnitaryChannel

end Quantum
