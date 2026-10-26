/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.Instrument
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

variable {d : ℕ}

/-- Conjugation by a matrix: `ρ ↦ U ρ U*ᴴ` as a linear map. -/
def conjugate (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun ρ := U * ρ * Uᴴ
  map_add' ρ₁ ρ₂ := by simp [mul_add, add_mul]
  map_smul' c ρ := by
    change U * (c • ρ) * Uᴴ = c • (U * ρ * Uᴴ)
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

/-- `conjugate U ρ = U * ρ * Uᴴ`. -/
@[grind =]
theorem conjugate_apply (U ρ : Matrix (Fin d) (Fin d) ℂ) :
    conjugate U ρ = U * ρ * Uᴴ := rfl

/-- The unitary channel `ρ ↦ U ρ Uᴴ` as an instrument with the single
outcome `()`. -/
def unitaryChannel (U : Matrix.unitaryGroup (Fin d) ℂ) : QComp d Unit where
  branch _ := conjugate (U : Matrix (Fin d) (Fin d) ℂ)
  branch_psd _ ρ hρ := by
    simp only [conjugate_apply]
    exact hρ.mul_mul_conjTranspose_same (U : Matrix (Fin d) (Fin d) ℂ)
  branch_summable _ :=
    summable_of_ne_finset_zero (s := {()}) (fun b hb => by simp at hb)
  branch_stp ρ hρ := by
    have htrace : (conjugate (U : Matrix (Fin d) (Fin d) ℂ) ρ).trace = ρ.trace := by
      rw [conjugate_apply, trace_mul_cycle]
      have hU := UnitaryGroup.star_mul_self U
      simp only [star_eq_conjTranspose] at hU
      rw [hU, Matrix.one_mul]
    rw [tsum_eq_single () (fun b hb => absurd rfl hb), htrace]

/-- The unitary channel of `U` followed by the unitary channel of `V` is the
unitary channel of `V * U`. -/
theorem unitaryChannel_compose
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    QComp.qbind (unitaryChannel U) (fun _ => unitaryChannel V) =
      unitaryChannel (V * U) := by
  apply QComp.ext_fun; intro () ρ
  change ∑' (_ : Unit), conjugate (V : Matrix _ _ ℂ) (conjugate (U : Matrix _ _ ℂ) ρ) =
    conjugate ((V * U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix _ _ ℂ) ρ
  rw [tsum_eq_single () (fun b hb => absurd rfl hb)]
  simp only [conjugate_apply, UnitaryGroup.mul_val, Matrix.conjTranspose_mul]
  simp only [← Matrix.mul_assoc]

end Quantum.UnitaryChannel
