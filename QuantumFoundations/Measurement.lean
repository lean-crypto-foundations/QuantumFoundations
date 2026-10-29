/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.Bridge.ToQComp
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Quantum Measurement as QComp

Defines POVMs and projective measurements as QComp instruments.

A POVM on a system with basis indexed by a finite type `d` and outcomes in `α`
is a family `{E_a}` of positive semidefinite matrices with `∑_a E_a = 1`. A family of measurement
operators `{M_a}` with `∑_a M_aᴴ M_a = 1` determines the instrument with
branches `ρ ↦ M_a ρ M_aᴴ`, whose POVM is `{M_aᴴ M_a}`.

## Main definitions

* `Quantum.Measurement.POVM`: a positive operator-valued measure.
* `Quantum.Measurement.MeasurementOps`: a complete family of measurement operators.
* `Quantum.Measurement.measureOps`: the instrument of a family of measurement
  operators.
* `Quantum.Measurement.ProjectiveMeasurement`, `Quantum.Measurement.projectiveMeasure`:
  measurement operators that are orthogonal projectors, and their instrument.
* `Quantum.Measurement.bornProb`: the Born-rule probability `tr(E_a ρ)`.

## Main results

* `Quantum.Measurement.bornProb_sum`: the Born-rule probabilities sum to `tr ρ`.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press,
  2018, Section 2.3.
* M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*,
  Cambridge University Press, 2000, Section 2.2.6.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix

noncomputable section

namespace Quantum.Measurement

variable {d : Type*} [Fintype d] [DecidableEq d] {α : Type}

/-! ## POVM -/

/-- A POVM (positive operator-valued measure) on a system with basis indexed by
`d`: a family of positive semidefinite matrices indexed by outcomes, summing to the
identity. -/
structure POVM (d : Type*) [Fintype d] [DecidableEq d] (α : Type) [Fintype α] where
  /-- The effect of outcome `a`. -/
  effect : α → Matrix d d ℂ
  /-- Every effect is positive semidefinite. -/
  effect_psd : ∀ a, (effect a).PosSemidef
  /-- The effects sum to the identity. -/
  sum_eq_one : ∑ a, effect a = 1

/-! ## Measurement Operators -/

/-- Measurement operators: a family `{M_a}` with `∑_a M_aᴴ M_a = 1`. The
associated POVM is `E_a = M_aᴴ M_a` and the unnormalized post-measurement state
on outcome `a` is `M_a ρ M_aᴴ`. -/
structure MeasurementOps (d : Type*) [Fintype d] [DecidableEq d] (α : Type) [Fintype α] where
  /-- The measurement operator of outcome `a`. -/
  op : α → Matrix d d ℂ
  /-- Completeness: `∑_a M_aᴴ M_a = 1`. -/
  completeness : ∑ a, (op a)ᴴ * op a = 1

/-- The instrument of a family of measurement operators, the image of their Kraus
subinstrument: branch `a` maps `ρ ↦ M_a ρ M_aᴴ`. -/
def measureOps [Fintype α] (M : MeasurementOps d α) : QComp d α :=
  (SubInstrument.ofKraus M.op M.completeness).toQComp

/-! ## Projective Measurement -/

/-- A projective measurement: measurement operators `P_a` that are orthogonal
projectors, `P_aᴴ = P_a` and `P_a * P_a = P_a`. -/
structure ProjectiveMeasurement (d : Type*) [Fintype d] [DecidableEq d] (α : Type) [Fintype α]
    extends MeasurementOps d α where
  /-- Every operator is self-adjoint. -/
  self_adjoint : ∀ a, (op a)ᴴ = op a
  /-- Every operator is idempotent. -/
  idempotent : ∀ a, op a * op a = op a

/-- The instrument of a projective measurement, the image of the Kraus subinstrument of its
projectors. -/
def projectiveMeasure [Fintype α] (P : ProjectiveMeasurement d α) :
    QComp d α :=
  (SubInstrument.ofKraus P.op P.completeness).toQComp

/-! ## Born Rule -/

/-- Born rule: the probability of outcome `a` when measuring the state `ρ`
with the POVM `{E_a}` is `tr(E_a ρ)`. -/
def bornProb [Fintype α] (E : POVM d α) (ρ : Matrix d d ℂ)
    (a : α) : ℂ :=
  (E.effect a * ρ).trace

/-- Born probabilities sum to `tr(ρ)`. -/
theorem bornProb_sum [Fintype α] (E : POVM d α)
    (ρ : Matrix d d ℂ) :
    ∑ a, bornProb E ρ a = ρ.trace := by
  simp only [bornProb]
  rw [show ∑ a : α, (E.effect a * ρ).trace =
    ((∑ a : α, E.effect a) * ρ).trace from by
    rw [Finset.sum_mul, trace_sum]]
  rw [E.sum_eq_one, Matrix.one_mul]

end Quantum.Measurement
