/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.Instrument
public import QuantumFoundations.CPMap
public import QuantumFoundations.TensorProduct
public import QuantumFoundations.PartialTrace
public import QuantumFoundations.PetzRecovery
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Quantum Markov Chains

A tripartite quantum state ρ_{ABC} forms a quantum Markov chain A → B → C
if and only if there exists a recovery channel R_{B→BC} such that
`(id_A ⊗ R)(ρ_{AB}) = ρ_{ABC}`. Equivalently, the conditional mutual
information `I(A:C|B) = 0`.

## Main Definitions

* `condMutualInfo` — conditional quantum mutual information I(A:C|B)
* `IsQuantumMarkovChain` — A → B → C Markov chain property
The recovery-channel characterisation of a Markov chain and the Fawzi–Renner
approximate-recovery bound are not stated; the comments in the recovery and
approximate-chain sections record what each needs.

## References

* Hayden et al. — *Structure of States Which Satisfy Strong Subadditivity*,
  CMP 246, 2004
* Fawzi & Renner — *Quantum Conditional Mutual Information and Approximate
  Markov Chains*, CMP 340, 2015
* Parzygnat & Buscemi — *Axioms for Retrodiction*, Quantum 7, 2023
-/

@[expose] public section

open scoped Matrix ComplexOrder ENNReal
open Matrix

noncomputable section

namespace Quantum.QuantumMarkovChain

open Quantum.TensorProduct
open Quantum.PartialTrace

variable {dA dB dC : ℕ}

/-! ## Von Neumann Entropy -/

/-- Von Neumann entropy of a density matrix: `S(ρ) = -tr(ρ log ρ)`.
    Defined via eigenvalues: `S(ρ) = -∑_i λ_i log(λ_i)` where `λ_i` are
    the eigenvalues of the Hermitian part of `ρ`.

    Uses `Real.negMulLog` which satisfies `negMulLog(x) = -x * log(x)` and
    `negMulLog(0) = 0`, correctly handling zero eigenvalues. -/
def vonNeumannEntropy {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) : ℝ :=
  ∑ i : Fin d, Real.negMulLog (hρ.1.eigenvalues i)

/-! ## Conditional Mutual Information -/

/-- **Conditional quantum mutual information** for a tripartite state ρ_{ABC}.

    `I(A:C|B) := S(AB) + S(BC) - S(ABC) - S(B)`

    where S is the von Neumann entropy and S(AB), S(BC), S(B) are entropies
    of the corresponding reduced states (partial traces).

    The marginals are computed as:
    - `ρ_AB` = tr_C(ρ) via `partialTrace₂` on `(dA*dB) x dC`
    - `ρ_BC` = tr_A(ρ) via `partialTrace₁` on `dA x (dB*dC)` after reindexing
    - `ρ_B`  = tr_A(ρ_AB) via `partialTrace₁` on `dA x dB` -/
def condMutualInfo
    (ρ : Matrix (Fin (dA * dB * dC)) (Fin (dA * dB * dC)) ℂ)
    (hρ : ρ.PosSemidef) : ℝ :=
  -- AB marginal: trace out C. Since dA*dB*dC = (dA*dB)*dC, use partialTrace₂.
  let ρ_AB := @partialTrace₂ (dA * dB) dC ρ
  let hρ_AB : ρ_AB.PosSemidef := @partialTrace₂_psd (dA * dB) dC ρ hρ
  -- B marginal from AB: trace out A.
  let ρ_B := @partialTrace₁ dA dB ρ_AB
  let hρ_B : ρ_B.PosSemidef := @partialTrace₁_psd dA dB ρ_AB hρ_AB
  -- BC marginal: reindex ρ as Fin (dA * (dB * dC)) then trace out A.
  let ρ_reindex := ρ.submatrix
    (Fin.cast (Nat.mul_assoc dA dB dC).symm) (Fin.cast (Nat.mul_assoc dA dB dC).symm)
  let hρ_reindex : ρ_reindex.PosSemidef := hρ.submatrix _
  let ρ_BC := @partialTrace₁ dA (dB * dC) ρ_reindex
  let hρ_BC : ρ_BC.PosSemidef := @partialTrace₁_psd dA (dB * dC) ρ_reindex hρ_reindex
  -- I(A:C|B) = S(AB) + S(BC) - S(ABC) - S(B)
  vonNeumannEntropy ρ_AB hρ_AB + vonNeumannEntropy ρ_BC hρ_BC
    - vonNeumannEntropy ρ hρ - vonNeumannEntropy ρ_B hρ_B

/-! ## Quantum Markov Chain -/

/-- A tripartite state ρ_{ABC} is a **quantum Markov chain** A → B → C
    if `I(A:C|B) = 0`, i.e., strong subadditivity is saturated. -/
def IsQuantumMarkovChain
    (ρ : Matrix (Fin (dA * dB * dC)) (Fin (dA * dB * dC)) ℂ)
    (hρ : ρ.PosSemidef) : Prop :=
  condMutualInfo ρ hρ = 0

/-! ## Recovery Channel Characterization -/

/-! The Hayden–Jozsa–Petz–Winter characterisation — ρ_{ABC} is a quantum Markov
    chain iff a recovery channel `R : B → BC` satisfies `(id_A ⊗ R)(ρ_{AB}) =
    ρ_{ABC}` — is not stated here. Its right-hand side needs the ampliation
    `id_A ⊗ R` of a channel on the `B` factor to the `AB` factor, and the
    tensor layer available to this module does not construct it. A form whose
    right-hand side omits that equation carries no condition on `R`: the
    existential is then satisfied by the zero map, and the biconditional makes
    every tripartite density matrix a Markov chain.

    **Reference**: P. Hayden, R. Jozsa, D. Petz, A. Winter, "Structure of
    states which satisfy strong subadditivity of quantum entropy with
    equality", Comm. Math. Phys. 246 (2004), 359-374. -/

/-! ## Approximate Markov Chains

The Fawzi–Renner theorem is not stated here. It says that for every ρ_{ABC} there exists
some channel `R : B → BC` with `F(ρ_{ABC}, (id_A ⊗ R)(ρ_{AB})) ≥ 2^{-I(A:C|B)/2}`, where `F`
is the fidelity `‖√ρ √σ‖₁` and `I(A:C|B)` is measured in bits; with the natural logarithms of
`condMutualInfo` the bound reads `exp(-I(A:C|B)/2)`. Fawzi and Renner prove existence of a
channel, not that the Petz map achieves the bound; Junge, Renner, Sutter, Wilde and Winter
show that a universal recovery map, an average of rotated Petz maps, does. Stating it needs the
ampliation `id_A ⊗ R` and the fidelity, neither of which this module constructs.

**References**: O. Fawzi, R. Renner, "Quantum Conditional Mutual Information
and Approximate Markov Chains", Comm. Math. Phys. 340 (2015), 575-611;
M. Junge, R. Renner, D. Sutter, M. M. Wilde, A. Winter, "Universal recovery maps and
approximate sufficiency of quantum relative entropy", Ann. Henri Poincaré 19 (2018). -/

end Quantum.QuantumMarkovChain
