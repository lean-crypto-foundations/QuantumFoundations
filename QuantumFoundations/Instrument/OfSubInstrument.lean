/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.Instrument
public import QuantumFoundations.SubInstrument

/-!
# Subinstruments as positive instruments

A `SubInstrument d d α` has completely positive branches whose finite partial sums of traces are
bounded by the trace of the input. Its branches are in particular positive, summable, and their
summed trace is bounded, so it is a `QComp d α` (`SubInstrument.toQComp`).

The instrument of a finite family of Kraus operators, `QComp.ofKraus`, is the image of the Kraus
subinstrument `SubInstrument.ofKraus`.

## Main definitions

* `Quantum.SubInstrument.toQComp`: a subinstrument on `d` as a positive instrument.
* `Quantum.QComp.ofKraus`: the instrument of a finite family of Kraus operators.

## Main results

* `Quantum.SubInstrument.toQComp_branch`: the branches of `p.toQComp` are those of `p`.
* `Quantum.QComp.ofKraus_branch`: branch `a` of `QComp.ofKraus M h` is `ρ ↦ M a ρ (M a)ᴴ`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder
open Matrix

noncomputable section

namespace Quantum

variable {d : Type*} [Fintype d] {α : Type}

namespace SubInstrument

/-- A subinstrument on `d` as a positive instrument: the same branches, which are positive
because they are completely positive. -/
def toQComp (p : SubInstrument d d α) : QComp d α where
  branch := p.branch
  branch_psd a _ hρ := p.posSemidef_branch_apply a hρ
  branch_summable := p.summable_branch_apply
  branch_stp ρ hρ := by
    rw [p.isCPTNIFamily.re_tsum_trace_apply]
    exact p.tsum_trace_re_le hρ

/-- The branches of `p.toQComp` are those of `p`. -/
@[simp]
theorem toQComp_branch (p : SubInstrument d d α) : p.toQComp.branch = p.branch :=
  rfl

end SubInstrument

/-- The instrument of a finite family of Kraus operators `M` with `∑ a, (M a)ᴴ M a = 1`: the
image of the Kraus subinstrument, whose branch `a` maps `ρ ↦ M a ρ (M a)ᴴ`. -/
def QComp.ofKraus [DecidableEq d] [Fintype α] (M : α → Matrix d d ℂ)
    (h_complete : ∑ a, (M a)ᴴ * M a = 1) : QComp d α :=
  (SubInstrument.ofKraus M h_complete).toQComp

/-- `QComp.ofKraus` branch unfolds to conjugation. -/
@[simp]
theorem QComp.ofKraus_branch [DecidableEq d] [Fintype α] (M : α → Matrix d d ℂ)
    (h : ∑ a, (M a)ᴴ * M a = 1) (a : α) (ρ : Matrix d d ℂ) :
    (QComp.ofKraus M h).branch a ρ = M a * ρ * (M a)ᴴ := rfl

end Quantum
