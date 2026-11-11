# QuantumFoundations

Finite-dimensional quantum information for cryptographic proofs in Lean 4, on Mathlib only.
Shared by [CatCrypt](https://github.com/spitters/CatCrypt-core) and
[VCVio](https://github.com/Verified-zkEVM/VCVio).
Results we intend to contribute to the `QuantumInfo` library of
[Physlib](https://github.com/leanprover-community/physlib) are listed, with what each still
needs, in `QuantumFoundations/ForPhyslib/README.md`.

This contribution holds CatCrypt-core's quantum foundation (Lean v4.35.0, Mathlib v4.35.0):

| Module | Content |
|---|---|
| `CPMap` | completely positive maps on matrices over a finite index type, effects, the trace dual of a linear map |
| `MatrixMap/Dual` | the trace dual of a matrix map: functoriality, Kraus maps, trace conditions |
| `MatrixMap/Stinespring` | unitary Stinespring dilations of channels; purifications |
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
| `Bridge/CPMap` | `CPMap` and `MatrixMap` agree: CP, TP, sub-TP, Choi's theorem, trace duals, channels |
| `ForMathlib/MatrixPosSemidef` | `Re z ≤ √c` from `normSq z ≤ c` (a Mathlib candidate) |

States, instruments, measurements and CP maps take the index of the system as any finite type.
Two register conventions coexist. `PartialTrace` and `TensorProduct` flatten a bipartite system
to `Fin (d₁ * d₂)`. The `MatrixMap` modules, including `MatrixMap/Stinespring`, index it by a
product type `A × R` and discard the right factor with `traceRight`. `Bridge/CPMap` already
relates `CPMap` to `MatrixMap`. Unifying the instruments with VCVio's `SubInstrument` (CP
branches) is the remaining work, in #17.

## From VCVio

| Module | Content |
|---|---|
| `MatrixMap` | matrix maps, complete positivity, trace bounds, and partial traces |
| `MatrixMap/Family`, `MatrixMap/Kraus` | summable families of maps and Kraus representations |
| `MatrixMap/Norm`, `MatrixMap/OpNorm`, `MatrixMap/BlockNorm` | trace, operator and block norm bounds |
| `MatrixMap/Completion` | matrix completion without increasing the operator norm (Parrott's theorem) |
| `MatrixMap/PinchingCompletion` | matrix completion localized to invariant blocks |
| `MatrixMap/Conjugation` | Kraus maps under amplification, partial traces and diagonal projections |
| `MatrixMap/Pinching`, `MatrixMap/Commutant` | pinching maps and commutation bounds |
| `MatrixMap/Comparison` | replacing Kraus operators before a trace-nonincreasing finishing map |
| `MatrixMap/ProjectorEvent`, `MatrixMap/ProjectorPair` | projector events and pairs of projectors |
| `DSubInstrument`, `SubInstrument` | instruments with dependent or fixed output registers |
| `Subsystem` | a register factored as a selected register and its complement |
| `SubInstrument/Subsystem` | subinstruments acting on a subsystem, leaving its complement unchanged |
| `SubInstrument/Relabel`, `DSubInstrument/Relabel` | transporting input and output bases along equivalences |
| `DSubInstrument/Observe` | outcome measures under framing, relabelling and continuations |
| `Register` | finite quantum registers |
| `Pure/Vector`, `Pure/Norm` | state vectors, matrix actions, and norm bounds |
| `ForMathlib/Analysis/Matrix/PosSemidef` | bounds for positive semidefinite matrices; block-diagonal positivity |
| `ForMathlib/Analysis/Matrix/Contraction` | contractions, isometries and Kronecker-product identities |
| `ForMathlib/Algebra/Group/Conj` | conjugation by an involution in a monoid |
| `ForMathlib/Analysis/Normed/Ring/Commutator` | norm bounds for commutators |
| `Observe` | substates, post-measurement states, and Born outcome measures |
| `Pure/State`, `Pure/Instrument`, `Pure/Tensor` | pure states, measurements, and tensors |
| `Oracle/Basis`, `Oracle/Unitary` | computational-basis operations and unitary oracle gates |

## License

Dual-licensed under the MIT license (`LICENSE-MIT`) or the Apache License 2.0
(`LICENSE-APACHE`), at your option. Unless you state otherwise, any contribution you submit for
inclusion is dual-licensed on the same terms.
