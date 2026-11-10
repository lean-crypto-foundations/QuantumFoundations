/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.Oracle.Basis

/-!
# Relabelling dependent outputs

Transport each outcome-dependent output basis along its own equivalence.
-/

public section

open Matrix
open scoped ComplexOrder

namespace Quantum

namespace DSubInstrument

variable {A ι : Type*} [Fintype A] {B C : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]

/-- Relabel the output system of the branch at `i` along `e i : B i ≃ C i`. -/
@[expose]
noncomputable def relabelOut (p : DSubInstrument A ι B) (e : ∀ i, B i ≃ C i) :
    DSubInstrument A ι C := by
  classical
  exact p.bind fun i ↦ DSubInstrument.bind (SubInstrument.relabel (e i)) fun _ ↦ ret C i

/-- The branch at `i` of a relabelled subinstrument relabels the branch of `p` at `i`. -/
@[simp]
theorem relabelOut_branch_apply (p : DSubInstrument A ι B) (e : ∀ i, B i ≃ C i) (i : ι)
    (ρ : Matrix A A ℂ) :
    (p.relabelOut e).branch i ρ = (p.branch i ρ).submatrix (e i).symm (e i).symm := by
  classical
  rw [relabelOut, branch_bind_bind_unit_ret, LinearMap.comp_apply,
    SubInstrument.relabel_branch_apply]

/-- Relabelling the outputs preserves losslessness. -/
theorem Lossless.relabelOut {p : DSubInstrument A ι B} (hp : p.Lossless) (e : ∀ i, B i ≃ C i) :
    (p.relabelOut e).Lossless := by
  classical
  exact hp.bind fun i ↦
    Lossless.bind (SubInstrument.lossless_relabel (e i)) fun _ ↦ lossless_ret _ _

/-- Sequencing after relabelled outputs relabels before each continuation. -/
theorem relabelOut_bind [∀ i, DecidableEq (B i)] [∀ i, DecidableEq (C i)]
    {κ : Type*} {D : κ → Type*} [∀ k, Fintype (D k)]
    (p : DSubInstrument A ι B) (e : ∀ i, B i ≃ C i) (k : (i : ι) → DSubInstrument (C i) κ D) :
    (p.relabelOut e).bind k =
      p.bind fun i ↦ DSubInstrument.bind (SubInstrument.relabel (e i)) fun _ ↦ k i := by
  refine DSubInstrument.ext (funext fun c ↦ LinearMap.ext fun ρ ↦ ?_)
  rw [branch_bind_apply, branch_bind_apply]
  refine tsum_congr fun i ↦ ?_
  rw [branch_bind_unit, LinearMap.comp_apply, SubInstrument.relabel_branch_apply,
    relabelOut_branch_apply]

end DSubInstrument

end Quantum
