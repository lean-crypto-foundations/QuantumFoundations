/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.TraceNorm

/-!
# Pure-target overlap lower bound for trace distance (one Fuchs–van de Graaf inequality)

For a pure target — a rank-one projector `P` (Hermitian idempotent with unit
trace, i.e. `|ψ⟩⟨ψ|`) — and a density matrix `ρ`, the **overlap fidelity** is
`F(P, ρ) = Tr(P ρ) = ⟨ψ|ρ|ψ⟩`.

This file proves the **easy Fuchs–van de Graaf direction**

  `1 − F(P, ρ) ≤ traceDist P ρ`,

i.e. low fidelity forces the states apart in trace distance (equivalently:
trace-distance closeness implies high fidelity). The proof is operational: the
target projector `P` is itself an effect, and it distinguishes `P` from `ρ` with
advantage `1 − F`, which the trace distance dominates by the Helstrom bound
`effect_trace_le`.

The harder direction `traceDist ≤ √(1 − F)` (high fidelity ⇒ indistinguishable)
needs Uhlmann's theorem / the square-root fidelity and is not proved here.
-/

@[expose] public section

set_option autoImplicit false

namespace Quantum.FuchsVanDeGraaf

open Quantum
open scoped Matrix ComplexOrder

variable {d : ℕ}

/-- Overlap fidelity with a pure target: `F(P, ρ) = Tr(P ρ)`. -/
noncomputable def fidelityPure (P ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (P * ρ).trace.re

/-- A Hermitian idempotent (an orthogonal projector) is an effect: both `P` and
`1 − P` are positive semidefinite. -/
theorem isEffect_of_projector (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.PosSemidef) (hidem : P * P = P) : IsEffect P := by
  refine ⟨hP, ?_⟩
  have hherm : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.isHermitian]
  have hmul : (1 - P) * (1 - P) = 1 - P := by
    rw [mul_sub, Matrix.mul_one, sub_mul, Matrix.one_mul, hidem, sub_self, sub_zero]
  have hself : (1 - P) = (1 - P)ᴴ * (1 - P) := by rw [hherm, hmul]
  rw [hself]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **Easy Fuchs–van de Graaf inequality.** For a pure target projector `P`
(`P² = P`, unit trace) and a density matrix `ρ` (unit trace),
`1 − F(P, ρ) ≤ traceDist P ρ`. -/
theorem one_sub_fidelity_le_traceDist (P ρ : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.PosSemidef) (hidem : P * P = P) (hPtr : P.trace = 1)
    (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1)
    (hherm : (P - ρ).IsHermitian) :
    1 - fidelityPure P ρ ≤ traceDist P ρ hP hρ hherm := by
  have hE : IsEffect P := isEffect_of_projector P hP hidem
  have htr0 : (P - ρ).trace = 0 := by rw [Matrix.trace_sub, hPtr, hρtr, sub_self]
  have hbound := effect_trace_le (P - ρ) hherm htr0 P hE
  have hlhs : (P * (P - ρ)).trace.re = 1 - fidelityPure P ρ := by
    rw [mul_sub, hidem, Matrix.trace_sub, Complex.sub_re, hPtr]
    simp only [Complex.one_re, fidelityPure]
  rw [hlhs] at hbound
  rw [traceDist]
  exact hbound

end Quantum.FuchsVanDeGraaf
