/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.QRHL

/-!
# Completely positive branches of basic instruments

The zero map and the branches of the trivial instrument are completely
positive; the tensor of two instruments is their sequential composite through
the local liftings; the two-outcome projective measurement `{P, 1 - P}` has
completely positive branches.

## Main definitions

* `Quantum.QComp.tensor`: the tensor of two instruments with completely positive
  branches, `QRHL.jointEvolve`.
* `Quantum.GentleMeasurement.Projector`: a self-adjoint idempotent matrix.
* `Quantum.measureProj`: the projective instrument `{P, 1 - P}`.

## Main results

* `Quantum.isCPMap_zero`: the zero map is completely positive.
* `Quantum.qpure_branch_isCPMap`: every branch of `QComp.qpure` is completely
  positive.
* `Quantum.QComp.tensor_def`: the tensor is `localOp₁ C` followed by `localOp₂ D`.
* `Quantum.measureProj_branch_isCPMap`: every branch of the projective
  instrument is completely positive.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder
open Matrix

noncomputable section

namespace Quantum

open Quantum.TensorProduct

/-! ## The trivial branches -/

/-- The zero map is completely positive. -/
theorem isCPMap_zero {n : Type*} [Fintype n] [DecidableEq n] :
    IsCPMap (0 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) := by
  intro k M _
  have h : tensorIdMap
      (0 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) k M = 0 := by
    funext p q
    change ((0 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
      (blockMatrix M p.1 q.1)) p.2 q.2 = 0
    simp
  rw [h]
  exact Matrix.PosSemidef.zero

open Classical in
/-- Every branch of the trivial instrument `qpure a₀` is completely positive:
it is `id` on the outcome `a₀` and `0` elsewhere. -/
theorem qpure_branch_isCPMap {n : Type*} [Fintype n] [DecidableEq n] {α : Type} (a₀ : α) :
    ∀ a, IsCPMap ((QComp.qpure (d := n) a₀).branch a) := by
  intro a
  change IsCPMap (if a = a₀ then LinearMap.id else 0)
  split_ifs with h
  · exact isCPMap_id
  · exact isCPMap_zero

/-! ## The tensor of instruments -/

section Tensor

variable {d e : ℕ} {α β : Type}

/-- The tensor of instruments: `C` on the first register and `D` on the
second register of the `d * e`-dimensional system, with outcome pair
`(a, b)`. It is `QRHL.jointEvolve`. -/
def QComp.tensor (C : QComp (Fin d) α) (D : QComp (Fin e) β)
    (hC : ∀ a, IsCPMap (C.branch a)) (hD : ∀ b, IsCPMap (D.branch b)) :
    QComp (Fin (d * e)) (α × β) :=
  QRHL.jointEvolve C D hC hD

/-- The tensor of `C` and `D` runs `localOp₁ C`, then `localOp₂ D`, and returns
the pair of outcomes. -/
theorem QComp.tensor_def (C : QComp (Fin d) α) (D : QComp (Fin e) β)
    (hC : ∀ a, IsCPMap (C.branch a)) (hD : ∀ b, IsCPMap (D.branch b)) :
    C.tensor D hC hD =
      QComp.qbind (localOp₁ C hC) fun a =>
        QComp.qbind (localOp₂ D hD) fun b => QComp.qpure (a, b) := rfl

end Tensor

end Quantum

namespace Quantum.GentleMeasurement

/-- A projector on a system with basis indexed by `d`: self-adjoint and idempotent. -/
structure Projector (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The underlying matrix. -/
  val : Matrix d d ℂ
  /-- The matrix is self-adjoint. -/
  self_adjoint : valᴴ = val
  /-- The matrix is idempotent. -/
  idempotent : val * val = val

end Quantum.GentleMeasurement

namespace Quantum

open Quantum Quantum.GentleMeasurement

/-- The projective measurement `{P, 1 - P}` as a quantum instrument: outcome
`true` is the branch `P ρ P`, outcome `false` the branch
`(1 - P) ρ (1 - P)`. -/
def measureProj {d : Type*} [Fintype d] [DecidableEq d] (P : Projector d) : QComp d Bool :=
  QComp.ofKraus (fun b => if b then P.val else 1 - P.val)
    (by
      rw [Fintype.sum_bool]
      change P.valᴴ * P.val + (1 - P.val)ᴴ * (1 - P.val) = 1
      have hsaQ : (1 - P.val)ᴴ = 1 - P.val := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
          P.self_adjoint]
      rw [P.self_adjoint, hsaQ, P.idempotent]
      have hQ : (1 - P.val) * (1 - P.val) = 1 - P.val := by
        rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, one_mul, mul_one,
          one_mul, P.idempotent]
        abel
      rw [hQ]
      abel)

/-- The branch of `measureProj P` at `true` is `ρ ↦ P ρ P`. -/
theorem measureProj_branch_true {d : Type*} [Fintype d] [DecidableEq d] (P : Projector d)
    (ρ : Matrix d d ℂ) :
    (measureProj P).branch true ρ = P.val * ρ * P.val := by
  change (if true then P.val else 1 - P.val) * ρ *
    (if true then P.val else 1 - P.val)ᴴ = _
  rw [ite_eq_left rfl, P.self_adjoint]

/-- The branch of `measureProj P` at `false` is `ρ ↦ (1 - P) ρ (1 - P)`. -/
theorem measureProj_branch_false {d : Type*} [Fintype d] [DecidableEq d] (P : Projector d)
    (ρ : Matrix d d ℂ) :
    (measureProj P).branch false ρ = (1 - P.val) * ρ * (1 - P.val) := by
  change (if false then P.val else 1 - P.val) * ρ *
    (if false then P.val else 1 - P.val)ᴴ = _
  rw [ite_eq_right Bool.false_ne_true, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, P.self_adjoint]

/-- Each branch of the projective instrument is completely positive. -/
theorem measureProj_branch_isCPMap {d : Type*} [Fintype d] [DecidableEq d] (P : Projector d) :
    ∀ b, IsCPMap ((measureProj P).branch b) := by
  intro b
  cases b
  · exact isCPMap_conj (1 - P.val) _ fun ρ => by
      rw [measureProj_branch_false, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, P.self_adjoint]
  · exact isCPMap_conj P.val _ fun ρ => by
      rw [measureProj_branch_true, P.self_adjoint]

end Quantum

end
