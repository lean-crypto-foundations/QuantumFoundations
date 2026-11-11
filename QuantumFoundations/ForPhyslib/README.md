# ForPhyslib

This directory holds results that the `QuantumInfo` library of
[Physlib](https://github.com/leanprover-community/physlib) lacks and that we intend to
contribute there (see
[issue #7](https://github.com/lean-crypto-foundations/QuantumFoundations/issues/7)).
QuantumFoundations does not depend on Physlib.

A result moves here when its statement uses only Mathlib definitions, over an arbitrary finite
index type `d` (`Matrix d d ℂ` with `[Fintype d]`), so that the Physlib version is a
restatement over `MState`, `CPTPMap` or `HermitianMat`. Modules here import Mathlib and other
QuantumFoundations modules only.

## Candidates

The candidates below are checked against Physlib v4.35.0. Their statements are already over an
arbitrary finite index type, but they still use definitions of QuantumFoundations:
`traceNormH` and `traceDist` (`TraceNorm`), `fidelityPure` (`FuchsVanDeGraaf`), `Projector`
(`InstrumentCP`), and `IsPositiveMap`, `IsCPMap`, `IsSTP` and `dualMap` (`CPMap`). A result
moves here once it is restated with these definitions unfolded into Mathlib ones.

| Result | Current location | Physlib v4.35.0 |
|---|---|---|
| Helstrom bound on matrices: an effect attains the trace norm of a traceless Hermitian matrix (`exists_effect_achieves`, `helstrom_traceless`) | `TraceNorm` | an abstract bound in `Physlib/ProbabilisticTheory/State/Discrimination.lean`, with no instance for `HermitianMat` |
| `1 − F(P, ρ) ≤ traceDist P ρ` for a pure target (`one_sub_fidelity_le_traceDist`) | `FuchsVanDeGraaf` | none |
| Gentle measurement (`gentle_measurement`, `gentle_measurement_traceDist`) | `GentleMeasurement` | none |
| The Petz recovery map: complete positivity, trace non-increase, exact recovery, composition (`petzRecovery_isCPMap`, `petzRecovery_stp`, `petzRecovery_exact`, `petzRecovery_comp`) | `PetzRecovery` | none |
| Contraction of the trace norm and the trace distance under positive trace-nonincreasing maps, CPTP maps in particular (`traceNormH_map_le_of_isSTP`, `traceDist_map_le_of_isSTP`, `traceNormH_map_le`, `traceDist_map_le`) | `TraceDistance` | none |
