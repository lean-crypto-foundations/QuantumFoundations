# QuantumFoundations

Finite-dimensional quantum information for cryptographic proofs in Lean 4, on Mathlib only.
Shared by [CatCrypt](https://github.com/spitters/CatCrypt-core) and
[VCVio](https://github.com/Verified-zkEVM/VCVio).

This contribution holds CatCrypt-core's quantum foundation (Lean v4.35.0, Mathlib v4.35.0):

| Module | Content |
|---|---|
| `CPMap` | completely positive maps on `Fin n` matrices, effects, the trace dual of a linear map |
| `DualMap` | functoriality of the trace dual (the Hilbert–Schmidt adjoint for positive maps) |
| `ChoiKraus` | the Choi matrix; every CP map has a Kraus form |
| `Stinespring` | the Stinespring dilation of a CPTP map by an ancilla |
| `PartialTrace` | partial traces over `Fin (d₁ * d₂)` |
| `TensorProduct` | Kronecker products of states and maps, local operations |
| `KroneckerPSD` | positivity of Kronecker products |
| `TraceNorm` | the trace norm and its bounds |
| `Measurement` | general and projective measurements as instruments |
| `UnitaryChannel` | unitary channels |
| `Instrument` | `QComp d α`: summable positive (not necessarily CP) branches, jointly sub-TP; the monad |
| `InstrumentCP` | complete positivity of instrument branches, tensor products of instruments |
| `QRHL` | a relational judgment on joint final states, outcomes summed out (not Unruh's qRHL) |

The planned merges with VCVio's `MatrixMap` and `SubInstrument` (registers as arbitrary finite
types, CP branches) are separate pull requests.

## License

Dual-licensed under the MIT license (`LICENSE-MIT`) or the Apache License 2.0
(`LICENSE-APACHE`), at your option. Unless you state otherwise, any contribution you submit for
inclusion is dual-licensed on the same terms.
