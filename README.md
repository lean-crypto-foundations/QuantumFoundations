# QuantumFoundations

Finite-dimensional quantum information for cryptographic proofs in Lean 4, on Mathlib only.
Shared by [CatCrypt](https://github.com/spitters/CatCrypt-core) and
[VCVio](https://github.com/Verified-zkEVM/VCVio).

This contribution holds CatCrypt-core's quantum foundation (Lean v4.35.0, Mathlib v4.35.0):

| Module | Content |
|---|---|
| `CPMap` | completely positive maps on `Fin n` matrices, effects, the dual map of a CP map |
| `DualMap` | the Hilbert–Schmidt adjoint of a linear map on matrices |
| `ChoiKraus` | the Choi matrix; every CP map has a Kraus form |
| `Stinespring` | the Stinespring dilation of a CPTP map by an ancilla |
| `PartialTrace` | partial traces over `Fin (d₁ * d₂)` |
| `TensorProduct` | Kronecker products of states and maps, local operations |
| `KroneckerPSD` | positivity of Kronecker products |
| `TraceNorm` | the trace norm and its bounds |
| `Measurement` | general and projective measurements as instruments |
| `UnitaryChannel` | unitary channels |
| `Instrument` | `QComp d α`: instruments with summable, jointly trace-nonincreasing branches; the lawful monad |
| `InstrumentCP` | complete positivity of instrument branches, tensor products of instruments |
| `QRHL` | quantum relational Hoare logic over instruments |
| `GentleMeasurement` | the gentle-measurement lemma for projective measurements |
| `FuchsVanDeGraaf` | `1 − F(P, ρ) ≤ traceDist P ρ` for a pure target `P` (one Fuchs–van de Graaf inequality) |
| `PetzRecovery` | the Petz recovery map, its exact recovery of the prior and compositionality |
| `QuantumBayes` | quantum Bayesian inversion by the Petz map, the Lüders (Jeffrey) update |
| `QuantumMarkovChain` | conditional quantum mutual information and quantum Markov chains |
| `MinEntropy` | the guessing probability and min-entropy of a finite distribution |
| `MinEntropyProduct` | additivity of min-entropy over independent registers |
| `MinEntropySplit` | conditional guessing probability; picking the better of two conditionings |
| `LeftoverHash` | the leftover hash lemma for a 2-universal hash family |
| `PrivacyAmplification` | privacy amplification in min-entropy form |
| `ForMathlib/MatrixPosSemidef` | positivity lemmas for complex matrices |

The planned merges with VCVio's `MatrixMap` and `SubInstrument` (registers as arbitrary finite
types, CP branches) are separate pull requests.

## License

Dual-licensed under the MIT license (`LICENSE-MIT`) or the Apache License 2.0
(`LICENSE-APACHE`), at your option. Unless you state otherwise, any contribution you submit for
inclusion is dual-licensed on the same terms.
