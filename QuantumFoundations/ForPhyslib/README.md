# ForPhyslib

This directory holds results that the `QuantumInfo` library of
[Physlib](https://github.com/leanprover-community/physlib) lacks and that we intend to
contribute there (see issue #7). QuantumFoundations does not depend on Physlib.

A result moves here when its statement uses only Mathlib types over an arbitrary finite
index type (`Matrix d d ℂ` with `[Fintype d] [DecidableEq d]`), so that the Physlib version
is a restatement over `MState`, `CPTPMap` or `HermitianMat`. Modules here import Mathlib
and other QuantumFoundations modules only.

Candidates, checked against Physlib v4.35.0:

| Result | Current location | Physlib v4.35.0 |
|---|---|---|
| Helstrom bound on matrices: an effect attains the trace norm of a traceless Hermitian matrix (`exists_effect_achieves`, `helstrom_traceless`) | `TraceNorm` | an abstract bound in `Physlib/ProbabilisticTheory/State/Discrimination.lean`, with no instance for `HermitianMat` |
| `1 − F(P, ρ) ≤ traceDist P ρ` for a pure target (`one_sub_fidelity_le_traceDist`) | `FuchsVanDeGraaf` | none |
| Gentle measurement (`gentle_measurement`, `gentle_measurement_traceDist`) | `GentleMeasurement` | none |
| The Petz recovery map: complete positivity, trace non-increase, exact recovery, composition (`petzRecovery_cp`, `petzRecovery_stp`, `petzRecovery_exact`, `petzRecovery_comp`) | `PetzRecovery` | none |
| Contraction of trace distance under CPTP maps | not yet proved; `exists_effect_achieves` and the dual map give it | none |

The modules above become candidates once their index types are general finite types.
