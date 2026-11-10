/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.DSubInstrument.Relabel

/-!
# Relabelling subinstruments

Transport input and output bases along equivalences, and commute relabelling with framing.
-/

public section

open Matrix
open scoped ComplexOrder

namespace Quantum

namespace SubInstrument

variable {A A' B B' : Type*} [Fintype A] [Fintype A'] [Fintype B] [Fintype B'] {α : Type*}

/-- Transport a subinstrument `p` from `A` to `B` along bijections `eA : A ≃ A'` and
`eB : B ≃ B'`: relabel `A'` back to `A`, run `p`, and relabel `B` to `B'`. -/
@[expose]
noncomputable def reindex (eA : A ≃ A') (eB : B ≃ B') (p : SubInstrument A B α) :
    SubInstrument A' B' α := by
  classical
  exact (relabel eA.symm).bind fun _ ↦ p.bind fun a ↦ (relabel eB).bind fun _ ↦ SubInstrument.pure a

/-- The branch of a transported subinstrument: move the input back along `eA`, apply the branch
of `p`, and move the output along `eB`. -/
theorem branch_reindex_apply (eA : A ≃ A') (eB : B ≃ B') (p : SubInstrument A B α) (a : α)
    (ρ : Matrix A' A' ℂ) :
    (p.reindex eA eB).branch a ρ = (p.branch a (ρ.submatrix eA eA)).submatrix eB.symm eB.symm := by
  classical
  rw [reindex, DSubInstrument.branch_bind_unit, DSubInstrument.branch_bind_bind_unit_ret,
    LinearMap.comp_apply,
    LinearMap.comp_apply, relabel_branch_apply, relabel_branch_apply, Equiv.symm_symm]

/-- A transported lossless subinstrument is lossless. -/
theorem Lossless.reindex {p : SubInstrument A B α} (hp : p.Lossless) (eA : A ≃ A')
    (eB : B ≃ B') : (p.reindex eA eB).Lossless := by
  classical
  exact (lossless_relabel _).bind fun _ ↦ hp.bind fun _ ↦
    (lossless_relabel _).bind fun _ ↦ DSubInstrument.lossless_ret _ _

end SubInstrument

namespace SubInstrument

open DSubInstrument

/-- A relabelling gate preserves the trace. -/
theorem trace_relabel_branch_apply {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] (e : X ≃ Y) (ρ : Matrix X X ℂ) :
    ((relabel e).branch () ρ).trace = ρ.trace := by
  rw [relabel_branch_apply]
  exact e.symm.sum_comp fun x ↦ ρ x x

/-- Framing a relabelling gate relabels the product along the bijection and the identity. -/
theorem frame_relabel {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (R : Type*) [Fintype R] [DecidableEq R] :
    (relabel e).frame R = relabel (e.prodCongr (Equiv.refl R)) :=
  DSubInstrument.ext <| funext fun u ↦ LinearMap.ext fun ρ ↦ by
    ext x y
    rw [branch_frame_apply, MatrixMap.amplify_apply, relabel_branch_apply, relabel_branch_apply]
    rfl

end SubInstrument

end Quantum
