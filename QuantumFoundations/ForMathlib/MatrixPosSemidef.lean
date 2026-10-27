/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# A bound on the real part of a complex number

A Mathlib candidate: `Complex.re_le_sqrt_of_normSq_le` belongs in
`Mathlib/Analysis/Complex/Norm.lean`.

## Main results

* `Complex.re_le_sqrt_of_normSq_le` — `Re z ≤ √c` whenever `|z|² ≤ c`.
-/

@[expose] public section

set_option autoImplicit false

namespace Complex

/-- The real part of a complex number is at most the square root of any
    upper bound on its squared modulus. -/
theorem re_le_sqrt_of_normSq_le {z : ℂ} {c : ℝ} (h : Complex.normSq z ≤ c) :
    z.re ≤ Real.sqrt c :=
  calc z.re ≤ ‖z‖ := Complex.re_le_norm z
    _ = Real.sqrt (Complex.normSq z) := Complex.norm_def z
    _ ≤ Real.sqrt c := Real.sqrt_le_sqrt h

end Complex
