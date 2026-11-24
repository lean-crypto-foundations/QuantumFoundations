/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.Subsystem
public import QuantumFoundations.SubInstrument.Relabel

/-!
# Subinstruments acting on a subsystem

Apply a subinstrument to a subsystem while leaving its complement unchanged.
Lifting respects nested factorizations, and branches on complementary subsystems commute.
-/

public section

open Matrix
open MeasureTheory
open scoped ComplexOrder

namespace Quantum

namespace SubInstrument

open DSubInstrument

variable {A B M : QReg} {α : Type*}

/-- **An instrument on a subsystem.** Apply `p` to the subsystem `S` of `M`: factor `M` as
`A × S.rest`, apply `p ⊗ id`, and undo the factorization. -/
@[expose]
noncomputable def lift (S : Subsystem A M) (p : SubInstrument A A α) : SubInstrument M M α :=
  (relabel S.equiv).bind fun _ ↦ (p.frame S.rest).relabelOut fun _ ↦ S.equiv.symm

/-- The branches of `p.lift S` are those of `p ⊗ id` conjugated by the factorization. -/
theorem lift_branch_apply (S : Subsystem A M) (p : SubInstrument A A α) (a : α)
    (ρ : Matrix M M ℂ) :
    (p.lift S).branch a ρ =
      ((p.branch a).amplify S.rest (ρ.submatrix S.equiv.symm S.equiv.symm)).submatrix
        S.equiv S.equiv := by
  rw [lift, SubInstrument.bind, branch_bind_unit, LinearMap.comp_apply, relabel_branch_apply,
    relabelOut_branch_apply, branch_frame_apply, Equiv.symm_symm]

/-- A subinstrument on a subsystem is lossless when the subinstrument is. -/
theorem Lossless.lift {p : SubInstrument A A α} (hp : p.Lossless) (S : Subsystem A M) :
    (p.lift S).Lossless :=
  (lossless_relabel _).bind fun _ ↦ DSubInstrument.Lossless.relabelOut (hp.frame _) _

/-- Lifting along a subsystem of a subsystem is lifting twice. -/
theorem lift_comp (T : Subsystem B M) (S : Subsystem A B) (p : SubInstrument A A α) :
    p.lift (T.comp S) = (p.lift S).lift T :=
  DSubInstrument.ext <| funext fun a ↦ LinearMap.ext fun ρ ↦ by
    ext m m'
    rw [lift_branch_apply, lift_branch_apply, submatrix_apply, submatrix_apply,
      MatrixMap.amplify_apply, MatrixMap.amplify_apply, lift_branch_apply, submatrix_apply,
      MatrixMap.amplify_apply]
    rfl

/-- On the whole register, the lift is the subinstrument itself. -/
@[simp]
theorem lift_whole (p : SubInstrument A A α) : p.lift (Subsystem.whole A) = p :=
  DSubInstrument.ext <| funext fun a ↦ LinearMap.ext fun ρ ↦ by
    ext m m'
    rw [lift_branch_apply, submatrix_apply, MatrixMap.amplify_apply]
    rfl

/-- The branches of a subinstrument on the complement of `S` act as `id ⊗ q` in the
factorization of `S`. -/
theorem lift_complement_branch_apply (S : Subsystem A M) {β : Type*}
    (q : SubInstrument S.rest S.rest β) (b : β) (ρ : Matrix M M ℂ) :
    (q.lift S.complement).branch b ρ =
      ((q.branch b).amplifyLeft A (ρ.submatrix S.equiv.symm S.equiv.symm)).submatrix
        S.equiv S.equiv := by
  ext m m'
  rw [lift_branch_apply, submatrix_apply, submatrix_apply, MatrixMap.amplify_apply,
    MatrixMap.amplifyLeft_apply]
  rfl

/-- **Compatibility.** A branch acting on a subsystem commutes with a branch acting on its
complement, as compatible references do. -/
theorem branch_lift_comm_complement (S : Subsystem A M) {β : Type*} (p : SubInstrument A A α)
    (q : SubInstrument S.rest S.rest β) (a : α) (b : β) :
    (p.lift S).branch a ∘ₗ (q.lift S.complement).branch b =
      (q.lift S.complement).branch b ∘ₗ (p.lift S).branch a := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, lift_complement_branch_apply,
    lift_complement_branch_apply, lift_branch_apply, lift_branch_apply, submatrix_submatrix,
    submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id, submatrix_id_id]
  exact congrArg (fun σ ↦ σ.submatrix S.equiv S.equiv) (LinearMap.congr_fun
    (MatrixMap.amplify_comp_amplifyLeft (p.branch a) (q.branch b)) _)

end SubInstrument

end Quantum
