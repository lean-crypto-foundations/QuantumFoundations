/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.MinEntropy

/-!
# Min-Entropy Splitting (Classical Combinatorial Core)

This file formalises the *classical* combinatorial core behind the **min-entropy
splitting lemma** of Damgård–Fehr–Renner–Salvail–Schaffner (DFRSS, CRYPTO 2007,
Lemma 3). We work entirely in the guessing-probability form of min-entropy
developed in `Quantum.MinEntropy`.

## Conditional guessing probability

For a joint (sub-)distribution `p : ι × κ → ℝ` the **conditional guessing
probability of the second coordinate given the first** is

  `condGuessProb p = ∑_{x : ι} max_{y : κ} p (x, y)`.

Operationally, this is the success probability of the optimal strategy that, on
seeing the conditioning value `x`, outputs the `y` maximising `p (x, y)`; summed
over the (unnormalised) weight that the joint distribution places on each `x`.
The associated **conditional min-entropy** is

  `condMinEntropy p = - log₂ (condGuessProb p)`.

(There is a symmetric `condGuessProb'` / `condMinEntropy'` conditioning on the
*second* coordinate, used to state the binary-choice splitting result.)

## What is proved here

The honest, fully-proved combinatorial content is the **monotonicity chain**
relating joint and conditional guessing probabilities:

* `guessProb_le_condGuessProb` / `guessProb_le_condGuessProb'` —
  `guessProb p ≤ condGuessProb p` (resp. `condGuessProb' p`): conditioning can
  only *increase* the guessing probability. This is the single genuinely
  combinatorial fact — the largest entry of the joint table is dominated by the
  sum of the per-row (per-column) maxima.
* `condMinEntropy_le_minEntropy` / `condMinEntropy'_le_minEntropy` — the
  min-entropy form: conditioning can only *decrease* min-entropy
  (`condMinEntropy p ≤ minEntropy p`).

and the **binary splitting selector**:

* `splitChoice p : Bool` — the deterministic choice rule, picking the coordinate
  whose conditional guessing probability is the smaller of `condGuessProb p`,
  `condGuessProb' p`.
* `selectedGuessProb_eq_min` — the selected conditional guessing probability is
  exactly `min (condGuessProb p) (condGuessProb' p)`.
* `condMinEntropy_selected_eq_max` — equivalently, the selected conditional
  min-entropy is `max (condMinEntropy p) (condMinEntropy' p)`: the splitting
  choice keeps the coordinate with the *larger* conditional min-entropy.
* `condMinEntropy_le_selected` — each individual conditional min-entropy is `≤`
  the selected one.

## Scope / honesty note (what is NOT proved)

This file proves the *tight* combinatorial core: the monotonicity chain and the
fact that the binary selector achieves `max (condMinEntropy p) (condMinEntropy'
p)`. It does **not** prove the full DFRSS bound `H_min(X_{1-C} | C) ≥ α/2`.

That bound requires the `√`-trick `PG(X₀) ≤ √ PG(X₀X₁)` (a Cauchy–Schwarz /
concavity step relating a marginal guessing probability to the square root of
the joint one), which turns the additive `α` into the `α/2` after the `-log₂`.
That square-root step over `Real.logb`/`sup'` is *not* formalised here. The
selector and the `max`/`min` chain delivered here are the exact (no-loss) part
of the argument; the `α/2` weakening is the separate, looser consequence that
the `√`-step would add on top, and it is explicitly out of scope.

## References

* Damgård, Fehr, Renner, Salvail, Schaffner — *A Tight High-Order Entropic
  Quantum Uncertainty Relation with Applications*, CRYPTO 2007, Lemma 3.
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

The single genuinely combinatorial fact: the largest entry of the whole joint
table is at most the *sum*, over rows `x`, of the largest entry in each row,
provided all entries are nonnegative. This is the monotonicity that conditioning
can only help the guesser. -/

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

/-! ### Binary splitting selector

The splitting lemma chooses a coordinate `C ∈ {0,1}` to *keep*; the adversary is
then handed the *other* coordinate as side information. We take the coordinate
whose conditional guessing probability (when it is the *guessed* side) is
smaller — equivalently, the kept side retains more min-entropy. -/

/-- **Deterministic splitting choice.** Returns `true` to keep the *second*
coordinate (condition on the first, i.e. use `condGuessProb`) when that gives the
smaller guessing probability, and `false` to keep the first coordinate
otherwise. The kept coordinate is the one whose conditional guessing probability
is `min (condGuessProb p) (condGuessProb' p)`. -/
def splitChoice (p : ι × κ → ℝ) : Bool :=
  decide (condGuessProb p ≤ condGuessProb' p)

/-- The guessing probability selected by `splitChoice` is the minimum of the two
conditional guessing probabilities. -/
theorem selectedGuessProb_eq_min (p : ι × κ → ℝ) :
    (if splitChoice p then condGuessProb p else condGuessProb' p)
      = min (condGuessProb p) (condGuessProb' p) := by
  unfold splitChoice
  by_cases hle : condGuessProb p ≤ condGuessProb' p
  · simp [hle]
  · have hle' : condGuessProb' p ≤ condGuessProb p := le_of_not_ge hle
    simp [hle, min_eq_right hle']

/-- The selected conditional guessing probability is bounded above by **both**
conditional guessing probabilities (it is their minimum). In particular it is at
most each, so the kept side never has *less* min-entropy than either conditional
min-entropy. -/
theorem selectedGuessProb_le_left (p : ι × κ → ℝ) :
    (if splitChoice p then condGuessProb p else condGuessProb' p)
      ≤ condGuessProb p := by
  rw [selectedGuessProb_eq_min]; exact min_le_left _ _

theorem selectedGuessProb_le_right (p : ι × κ → ℝ) :
    (if splitChoice p then condGuessProb p else condGuessProb' p)
      ≤ condGuessProb' p := by
  rw [selectedGuessProb_eq_min]; exact min_le_right _ _

/-- **Selected conditional min-entropy.** The conditional min-entropy of the
coordinate kept by `splitChoice`: `- log₂` of the *smaller* of the two
conditional guessing probabilities. By `condMinEntropy_selected_eq_max` below
this equals `max (condMinEntropy p) (condMinEntropy' p)`, i.e. the selector
keeps whichever coordinate carries the larger conditional min-entropy.

Each of `condMinEntropy p`, `condMinEntropy' p` is in turn `≤ minEntropy p`
(`condMinEntropy_le_minEntropy`), so conditioning lowers entropy on each side;
the selector's job is only to keep the *better* of the two sides. The further
`α/2` lower bound of DFRSS is out of scope (see module docstring). -/
def condMinEntropy_selected (p : ι × κ → ℝ) : ℝ :=
  - Real.logb 2 (if splitChoice p then condGuessProb p else condGuessProb' p)

/-- The selected conditional min-entropy is the **maximum** of the two
conditional min-entropies (since it minimises the guessing probability and
`-logb` is antitone). Thus the splitting choice keeps the coordinate with the
*more* conditional min-entropy — the operational point of the lemma. -/
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

/-- **Splitting selector keeps the larger-entropy coordinate.** The selected
conditional min-entropy is `≥` each individual conditional min-entropy. -/
theorem condMinEntropy_le_selected (p : ι × κ → ℝ)
    (h0 : 0 < condGuessProb p) (h1 : 0 < condGuessProb' p) :
    condMinEntropy p ≤ condMinEntropy_selected p ∧
      condMinEntropy' p ≤ condMinEntropy_selected p := by
  rw [condMinEntropy_selected_eq_max p h0 h1]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

end

end Quantum
