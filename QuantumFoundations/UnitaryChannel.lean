/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.Bridge.ToQComp
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitary Channels for QComp

Unitary evolution `ρ ↦ U ρ U*` as a QComp operation with deterministic
outcome (type `Unit`).

A unitary channel `Φ_U(ρ) = U ρ Uᴴ` has the single Kraus operator `U`; it is
trace-preserving by cyclicity of the trace.

## Main definitions

* `Quantum.UnitaryChannel.conjugate`: the linear map `ρ ↦ U ρ Uᴴ`.
* `Quantum.UnitaryChannel.unitaryChannel`: the instrument with the single
  outcome `()` whose branch is conjugation by a unitary `U`.

## Main results

* `Quantum.UnitaryChannel.unitaryChannel_compose`: the channel of `U` followed by
  the channel of `V` is the channel of `V * U`.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press,
  2018, Section 2.2.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix

noncomputable section

namespace Quantum.UnitaryChannel

variable {d : Type*} [Fintype d]

/-- Conjugation by a matrix: `ρ ↦ U ρ Uᴴ` as a linear map, the Kraus map of `U`. -/
def conjugate (U : Matrix d d ℂ) :
    Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ :=
  MatrixMap.conj U

/-- `conjugate U ρ = U * ρ * Uᴴ`. -/
@[grind =]
theorem conjugate_apply (U ρ : Matrix d d ℂ) :
    conjugate U ρ = U * ρ * Uᴴ := rfl

variable [DecidableEq d]

/-- The unitary channel `ρ ↦ U ρ Uᴴ` as an instrument with the single
outcome `()`: the image of the Kraus subinstrument with the single Kraus operator `U`. -/
def unitaryChannel (U : Matrix.unitaryGroup d ℂ) : QComp d Unit :=
  (SubInstrument.ofKraus (fun _ : Unit ↦ (U : Matrix d d ℂ))
    (by simpa only [Finset.univ_unique, Finset.sum_singleton, star_eq_conjTranspose] using
      UnitaryGroup.star_mul_self U)).toQComp

/-- The branch of the unitary channel of `U` maps `ρ ↦ U ρ Uᴴ`. -/
@[simp]
theorem unitaryChannel_branch (U : Matrix.unitaryGroup d ℂ) (u : Unit) (ρ : Matrix d d ℂ) :
    (unitaryChannel U).branch u ρ = (U : Matrix d d ℂ) * ρ * (U : Matrix d d ℂ)ᴴ := rfl

/-- The unitary channel of `U` followed by the unitary channel of `V` is the
unitary channel of `V * U`. -/
theorem unitaryChannel_compose
    (U V : Matrix.unitaryGroup d ℂ) :
    QComp.qbind (unitaryChannel U) (fun _ => unitaryChannel V) =
      unitaryChannel (V * U) := by
  apply QComp.ext_fun; intro () ρ
  change ∑' (_ : Unit), conjugate (V : Matrix _ _ ℂ) (conjugate (U : Matrix _ _ ℂ) ρ) =
    conjugate ((V * U : Matrix.unitaryGroup d ℂ) : Matrix _ _ ℂ) ρ
  rw [tsum_eq_single () (fun b hb => absurd rfl hb)]
  simp only [conjugate_apply, UnitaryGroup.mul_val, Matrix.conjTranspose_mul]
  simp only [← Matrix.mul_assoc]

end Quantum.UnitaryChannel
