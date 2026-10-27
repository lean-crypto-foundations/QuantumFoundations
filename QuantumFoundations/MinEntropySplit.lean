/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.MinEntropy

/-!
# Conditional guessing probability and choosing the better conditioning

For a joint (sub-)distribution `p : ι × κ → ℝ` this file defines the two
conditional guessing probabilities, proves that conditioning can only help the
guesser, and studies the deterministic rule that picks whichever of the two
conditionings has the smaller guessing probability. Everything is classical and
stated in the guessing-probability form of `QuantumFoundations.MinEntropy`.

## Conditional guessing probability

The **conditional guessing probability of the second coordinate given the
first** is

  `condGuessProb p = ∑_{x : ι} max_{y : κ} p (x, y)`,

the success probability of the guesser that, on seeing `x`, outputs the `y`
maximising `p (x, y)`. The associated conditional min-entropy is
`condMinEntropy p = - log₂ (condGuessProb p)`. The symmetric quantities
`condGuessProb'` and `condMinEntropy'` condition on the second coordinate and
guess the first.

## Main results

* `guessProb_le_condGuessProb` / `guessProb_le_condGuessProb'` —
  `guessProb p ≤ condGuessProb p` (resp. `condGuessProb' p`): the largest entry
  of the joint table is at most the sum of the per-row (per-column) maxima.
* `condMinEntropy_le_minEntropy` / `condMinEntropy'_le_minEntropy` — the
  min-entropy form: `condMinEntropy p ≤ minEntropy p`.
* `condChoice p : Bool` — one Boolean, fixed for the whole distribution, that
  selects the conditioning with the smaller guessing probability.
* `selectedGuessProb_eq_min` — the selected guessing probability is
  `min (condGuessProb p) (condGuessProb' p)`.
* `condMinEntropy_selected_eq_max` — the selected conditional min-entropy is
  `max (condMinEntropy p) (condMinEntropy' p)`.
* `condMinEntropy_le_selected` — each conditional min-entropy is at most the
  selected one.

This is not the min-entropy splitting lemma of Damgård–Fehr–Renner–Salvail–
Schaffner (CRYPTO 2007, Lemma 3), which bounds the joint smooth min-entropy of
`(X_{1-C}, C)` for a sample-dependent selector `C`.

## References

* König, Renner, Schaffner — *The operational meaning of min- and max-entropy*,
  IEEE Trans. Inf. Theory 2009.
-/

@[expose] public section

open scoped ENNReal

namespace Quantum

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]

/-- **Conditional guessing probability** of the *second* coordinate given the
first: `condGuessProb p = ∑_x max_y p (x, y)`. The optimal guesser, on seeing
the conditioning value `x`, outputs the most likely `y`. -/
def condGuessProb (p : ι × κ → ℝ) : ℝ :=
  ∑ x : ι, guessProb (fun y : κ => p (x, y))

/-- **Conditional guessing probability** of the *first* coordinate given the
second: `condGuessProb' p = ∑_y max_x p (x, y)`. -/
def condGuessProb' (p : ι × κ → ℝ) : ℝ :=
  ∑ y : κ, guessProb (fun x : ι => p (x, y))

/-- **Conditional min-entropy** (second given first):
`condMinEntropy p = - log₂ (condGuessProb p)`. -/
def condMinEntropy (p : ι × κ → ℝ) : ℝ :=
  - Real.logb 2 (condGuessProb p)

/-- **Conditional min-entropy** (first given second):
`condMinEntropy' p = - log₂ (condGuessProb' p)`. -/
def condMinEntropy' (p : ι × κ → ℝ) : ℝ :=
  - Real.logb 2 (condGuessProb' p)

/-! ### Nonnegativity -/

omit [Nonempty ι] in
/-- The conditional guessing probability of a nonnegative joint vector is
nonnegative. -/
theorem condGuessProb_nonneg {p : ι × κ → ℝ} (h : ∀ q, 0 ≤ p q) :
    0 ≤ condGuessProb p := by
  unfold condGuessProb
  refine Finset.sum_nonneg (fun x _ => ?_)
  exact guessProb_nonneg (fun y => h (x, y))

omit [Nonempty κ] in
/-- The conditional guessing probability (other side) of a nonnegative joint
vector is nonnegative. -/
theorem condGuessProb'_nonneg {p : ι × κ → ℝ} (h : ∀ q, 0 ≤ p q) :
    0 ≤ condGuessProb' p := by
  unfold condGuessProb'
  refine Finset.sum_nonneg (fun y _ => ?_)
  exact guessProb_nonneg (fun x => h (x, y))

/-! ### Conditioning increases guessing probability (decreases min-entropy)

The largest entry of the whole joint table is at most the *sum*, over rows `x`,
of the largest entry in each row, provided all entries are nonnegative. -/

/-- **Conditioning increases guessing probability.** For a nonnegative joint
sub-distribution `p`, `guessProb p ≤ condGuessProb p`. The maximal single entry
`max_{x,y} p (x,y)` is bounded by `∑_x max_y p (x,y)`, since the maximising row's
contribution alone already dominates it and every other row contributes a
nonnegative amount. -/
theorem guessProb_le_condGuessProb {p : ι × κ → ℝ} (h : ∀ q, 0 ≤ p q) :
    guessProb p ≤ condGuessProb p := by
  -- `guessProb p = p (x₀, y₀)` for some witnessing pair.
  obtain ⟨q, hq⟩ := guessProb_mem_range p
  obtain ⟨x₀, y₀⟩ := q
  rw [hq]
  -- `p (x₀, y₀) ≤ max_y p (x₀, y) = guessProb (row x₀)`.
  have hrow : p (x₀, y₀) ≤ guessProb (fun y : κ => p (x₀, y)) :=
    le_guessProb (fun y : κ => p (x₀, y)) y₀
  refine le_trans hrow ?_
  -- That single row term is `≤` the full sum of nonnegative row maxima.
  unfold condGuessProb
  refine Finset.single_le_sum (f := fun x : ι => guessProb (fun y : κ => p (x, y)))
    (fun x _ => guessProb_nonneg (fun y => h (x, y))) (Finset.mem_univ x₀)

/-- Symmetric version: `guessProb p ≤ condGuessProb' p`. -/
theorem guessProb_le_condGuessProb' {p : ι × κ → ℝ} (h : ∀ q, 0 ≤ p q) :
    guessProb p ≤ condGuessProb' p := by
  obtain ⟨q, hq⟩ := guessProb_mem_range p
  obtain ⟨x₀, y₀⟩ := q
  rw [hq]
  have hcol : p (x₀, y₀) ≤ guessProb (fun x : ι => p (x, y₀)) :=
    le_guessProb (fun x : ι => p (x, y₀)) x₀
  refine le_trans hcol ?_
  unfold condGuessProb'
  refine Finset.single_le_sum (f := fun y : κ => guessProb (fun x : ι => p (x, y)))
    (fun y _ => guessProb_nonneg (fun x => h (x, y))) (Finset.mem_univ y₀)

/-- **Conditioning decreases min-entropy** (min-entropy form of
`guessProb_le_condGuessProb`): `condMinEntropy p ≤ minEntropy p`. Requires the
joint guessing probability to be strictly positive (so both `logb`s are taken at
positive arguments). -/
theorem condMinEntropy_le_minEntropy {p : ι × κ → ℝ} (h : ∀ q, 0 ≤ p q)
    (hpos : 0 < guessProb p) : condMinEntropy p ≤ minEntropy p := by
  unfold condMinEntropy minEntropy
  have hmono := guessProb_le_condGuessProb h
  have hcg : 0 < condGuessProb p := lt_of_lt_of_le hpos hmono
  -- `- logb 2 a ≤ - logb 2 b  ↔  logb 2 b ≤ logb 2 a`, and `logb` is monotone.
  rw [neg_le_neg_iff]
  exact Real.logb_le_logb_of_le (by norm_num) hpos hmono

/-- Symmetric min-entropy form: `condMinEntropy' p ≤ minEntropy p`. -/
theorem condMinEntropy'_le_minEntropy {p : ι × κ → ℝ} (h : ∀ q, 0 ≤ p q)
    (hpos : 0 < guessProb p) : condMinEntropy' p ≤ minEntropy p := by
  unfold condMinEntropy' minEntropy
  have hmono := guessProb_le_condGuessProb' h
  have hcg : 0 < condGuessProb' p := lt_of_lt_of_le hpos hmono
  rw [neg_le_neg_iff]
  exact Real.logb_le_logb_of_le (by norm_num) hpos hmono

/-! ### Choosing the better conditioning

Of the two conditionings, keep the one whose guessing probability is smaller,
equivalently whose conditional min-entropy is larger. The choice is a single
Boolean depending on `p` as a whole, not on a sample. -/

/-- **Choice of conditioning.** Returns `true` (condition on the first
coordinate and guess the second, i.e. use `condGuessProb`) when that guessing
probability is at most the other one, and `false` (use `condGuessProb'`)
if not. The selected guessing probability is therefore
`min (condGuessProb p) (condGuessProb' p)`. -/
def condChoice (p : ι × κ → ℝ) : Bool :=
  decide (condGuessProb p ≤ condGuessProb' p)

@[deprecated condChoice (since := "2026-10-27")]
alias splitChoice := condChoice

/-- The guessing probability selected by `condChoice` is the minimum of the two
conditional guessing probabilities. -/
theorem selectedGuessProb_eq_min (p : ι × κ → ℝ) :
    (if condChoice p then condGuessProb p else condGuessProb' p)
      = min (condGuessProb p) (condGuessProb' p) := by
  unfold condChoice
  by_cases hle : condGuessProb p ≤ condGuessProb' p
  · simp [hle]
  · have hle' : condGuessProb' p ≤ condGuessProb p := le_of_not_ge hle
    simp [hle, min_eq_right hle']

/-- The selected conditional guessing probability is at most `condGuessProb p`. -/
theorem selectedGuessProb_le_left (p : ι × κ → ℝ) :
    (if condChoice p then condGuessProb p else condGuessProb' p)
      ≤ condGuessProb p := by
  rw [selectedGuessProb_eq_min]; exact min_le_left _ _

/-- The selected conditional guessing probability is at most `condGuessProb' p`. -/
theorem selectedGuessProb_le_right (p : ι × κ → ℝ) :
    (if condChoice p then condGuessProb p else condGuessProb' p)
      ≤ condGuessProb' p := by
  rw [selectedGuessProb_eq_min]; exact min_le_right _ _

/-- **Selected conditional min-entropy.** `- log₂` of the guessing probability
selected by `condChoice`, i.e. of the smaller of the two conditional guessing
probabilities. By `condMinEntropy_selected_eq_max` it equals
`max (condMinEntropy p) (condMinEntropy' p)` when both guessing probabilities
are positive. -/
def condMinEntropy_selected (p : ι × κ → ℝ) : ℝ :=
  - Real.logb 2 (if condChoice p then condGuessProb p else condGuessProb' p)

/-- The selected conditional min-entropy is the **maximum** of the two
conditional min-entropies, since it minimises the guessing probability and
`- logb 2` is antitone on positive reals. -/
theorem condMinEntropy_selected_eq_max (p : ι × κ → ℝ)
    (h0 : 0 < condGuessProb p) (h1 : 0 < condGuessProb' p) :
    condMinEntropy_selected p = max (condMinEntropy p) (condMinEntropy' p) := by
  unfold condMinEntropy_selected condMinEntropy condMinEntropy'
  rw [selectedGuessProb_eq_min]
  -- `- logb 2 (min a b) = max (- logb 2 a) (- logb 2 b)` for `a, b > 0`.
  rcases le_total (condGuessProb p) (condGuessProb' p) with hle | hle
  · rw [min_eq_left hle]
    rw [max_eq_left]
    -- need: `- logb 2 (condGuessProb' p) ≤ - logb 2 (condGuessProb p)`
    rw [neg_le_neg_iff]
    exact Real.logb_le_logb_of_le (by norm_num) h0 hle
  · rw [min_eq_right hle]
    rw [max_eq_right]
    rw [neg_le_neg_iff]
    exact Real.logb_le_logb_of_le (by norm_num) h1 hle

/-- The selected conditional min-entropy is `≥` each individual conditional
min-entropy. -/
theorem condMinEntropy_le_selected (p : ι × κ → ℝ)
    (h0 : 0 < condGuessProb p) (h1 : 0 < condGuessProb' p) :
    condMinEntropy p ≤ condMinEntropy_selected p ∧
      condMinEntropy' p ≤ condMinEntropy_selected p := by
  rw [condMinEntropy_selected_eq_max p h0 h1]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

end

end Quantum
