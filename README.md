# QuantumFoundations

Finite-dimensional quantum information for cryptographic proofs in Lean 4, on Mathlib only.
Shared by [CatCrypt](https://github.com/spitters/CatCrypt-core) and
[VCVio](https://github.com/Verified-zkEVM/VCVio).

This contribution holds CatCrypt-core's quantum foundation (Lean v4.35.0, Mathlib v4.35.0):

| Module | Content |
|---|---|
| `CPMap` | completely positive maps on matrices over a finite index type, effects, the trace dual of a linear map |
| `DualMap` | functoriality of the trace dual (the Hilbert–Schmidt adjoint for positive maps) |
| `ChoiKraus` | the Choi matrix; every CP map has a Kraus form |
| `Stinespring` | the Stinespring dilation of a CPTP map by an ancilla |
| `PartialTrace` | partial traces over `Fin (d₁ * d₂)` |
| `TensorProduct` | Kronecker products of states and maps, local operations |
| `KroneckerPSD` | positivity of Kronecker products |
| `TraceNorm` | the trace norm and its bounds |
| `Measurement` | general and projective measurements as instruments |
| `UnitaryChannel` | unitary channels |
| `Instrument` | `QComp d α`: positive (maybe non-CP) branches, jointly sub-TP; a lawful monad |
| `InstrumentCP` | complete positivity of instrument branches, tensor products of instruments |
| `QRHL` | a relational judgment on joint final states, outcomes summed out (not Unruh's qRHL) |
| `GentleMeasurement` | the gentle-measurement lemma for projective measurements |
| `FuchsVanDeGraaf` | `1 − F(P, ρ) ≤ traceDist P ρ` for a pure target `P` (one Fuchs–van de Graaf inequality) |
| `PetzRecovery` | the Petz recovery map: complete positivity, trace, exact recovery, composition |
| `QuantumBayes` | the defining equation of the Petz map, the Lüders update by an effect |
| `QuantumMarkovChain` | conditional quantum mutual information and quantum Markov chains |
| `MinEntropy` | the guessing probability and min-entropy of a finite distribution |
| `MinEntropyProduct` | additivity of min-entropy over independent registers |
| `MinEntropySplit` | conditional guessing probability; picking the better of two conditionings |
| `LeftoverHash` | the leftover hash lemma for a 2-universal hash family |
| `PrivacyAmplification` | the classical leftover hash lemma in min-entropy form |
| `ForMathlib/MatrixPosSemidef` | `Re z ≤ √c` from `normSq z ≤ c` (a Mathlib candidate) |

States, instruments, measurements and CP maps take the index of the system as any finite type;
bipartite systems are encoded as `Fin (d₁ * d₂)`. The planned merges with VCVio's `MatrixMap`
and `SubInstrument` (CP branches) are separate pull requests.

## From VCVio

| Module | Content |
|---|---|
| `MatrixMap` | matrix maps, complete positivity, trace bounds, and partial traces |
| `MatrixMap/Family`, `MatrixMap/Kraus` | summable families of maps and Kraus representations |
| `MatrixMap/Norm`, `MatrixMap/OpNorm`, `MatrixMap/BlockNorm` | trace, operator and block norm bounds |
| `MatrixMap/Completion` | matrix completion without increasing the operator norm (Parrott's theorem) |
| `MatrixMap/Pinching`, `MatrixMap/Commutant` | pinching maps and commutation bounds |
| `MatrixMap/Comparison` | replacing Kraus operators before a trace-nonincreasing finishing map |
| `MatrixMap/ProjectorEvent`, `MatrixMap/ProjectorPair` | projector events and pairs of projectors |
| `DSubInstrument`, `SubInstrument` | instruments with dependent or fixed output registers |
| `Register` | finite quantum registers |
| `Pure/Vector`, `Pure/Norm` | state vectors, matrix actions, and norm bounds |
| `ForMathlib/Analysis/Matrix/PosSemidef` | bounds for positive semidefinite matrices |
| `ForMathlib/Analysis/Normed/Ring/Commutator` | norm bounds for commutators |
| `Observe` | substates, post-measurement states, and Born outcome measures |
| `Pure/State`, `Pure/Instrument`, `Pure/Tensor` | pure states, measurements, and tensors |
| `Oracle/Basis`, `Oracle/Unitary` | computational-basis operations and unitary oracle gates |

## Agreement of the two developments

| Module | Content |
|---|---|
| `Bridge/Instrument` | density matrices are the trace-one substates; instruments with completely positive branches are exactly the `QComp`s whose branches are completely positive (`SubInstrument.equivCP`), compatibly with `pure`, `bind`, `map` and `fail`; acceptance probability is the outcome measure of `{true}`; the Kraus, general, projective and unitary measurements of both sides agree |

## License

Dual-licensed under the MIT license (`LICENSE-MIT`) or the Apache License 2.0
(`LICENSE-APACHE`), at your option. Unless you state otherwise, any contribution you submit for
inclusion is dual-licensed on the same terms.
