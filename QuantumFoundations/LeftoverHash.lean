/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Bas Spitters
-/
module

public import QuantumFoundations.MinEntropy
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Field

/-!
# The Classical Leftover Hash Lemma

This file develops the *classical* Leftover Hash Lemma (LHL) over a finite
2-universal hash family, the standard randomness-extraction tool underlying
privacy amplification in QKD.

## Setup

Fix finite types `X` (source) and `Y` (target), a finite index type `I` for the
hash family, and a family `h : I → (X → Y)`. The family is **2-universal** if for
every pair of distinct sources `x ≠ x'`, a uniformly chosen `h` collides on them
with probability at most `1/|Y|`:

  `(#{ i | h i x = h i x' }) / |I| ≤ 1/|Y|`.

For a probability vector `p : X → ℝ` the **collision probability** is
`collisionProb p = ∑_x (p x)²`.

## Main results

* `TwoUniversalHashFamily` — the bundled structure (family + 2-universal axiom).
* `collisionProb` — `∑_x (p x)²`; `collisionProb_nonneg`, monotone facts.
* `expectedCollision_le` (**the engine of the LHL**) — the expected collision
  probability of the hashed variable `h(X)`, averaged over a uniform choice of
  `h` from a 2-universal family, satisfies

    `E_h[ ∑_y (∑_{x : h x = y} p x)² ] ≤ collisionProb p + 1/|Y|`.

* `leftover_hash_lemma` — the statistical distance of `(h, h(X))` from
  `(h, U_Y)` is at most `½ · √(|Y| · collisionProb p)`. Built on the collision
  engine via the Cauchy–Schwarz inequality `sq_sum_le_card_mul_sum_sq`.

The statistical distance here is the `ℓ¹`/total-variation form
`δ(D₁,D₂) = ½ ∑_z |D₁ z − D₂ z|` taken over the joint outcome `(h, y)`.

## References

* Impagliazzo, Levin, Luby — *Pseudo-random generation from one-way functions*,
  STOC 1989 (origin of the LHL).
* Renner, R. — *Security of Quantum Key Distribution*, PhD thesis, ETH 2005
  (the conditional, quantum-side-information LHL; this file proves only its classical
  unconditional special case).
* Tomamichel — *Quantum Information Processing with Finite Resources*, §5
  (collision-entropy / ℓ² formulation).
-/

@[expose] public section

namespace Quantum

noncomputable section

open Finset

/-! ## Collision probability of a finite probability vector -/

variable {X : Type*} [Fintype X]

/-- **Collision probability** of a probability vector `p : X → ℝ`:
`collisionProb p = ∑_x (p x)²`. This is the probability that two independent
draws from `p` agree, and equals `2^{-H₂(p)}` for the (Rényi-2) collision
entropy `H₂`. -/
def collisionProb (p : X → ℝ) : ℝ := ∑ x, (p x) ^ 2

/-- The collision probability is nonnegative. -/
theorem collisionProb_nonneg (p : X → ℝ) : 0 ≤ collisionProb p :=
  Finset.sum_nonneg (fun x _ => sq_nonneg (p x))

/-- For a sub-probability vector (`∑ p ≤ 1`, `0 ≤ p`), the collision probability
is `≤ 1`: each `(p x)² ≤ p x` since `p x ≤ 1`, and `∑ p ≤ 1`. -/
theorem collisionProb_le_one {p : X → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∀ x, p x ≤ 1) (hsum : ∑ x, p x ≤ 1) : collisionProb p ≤ 1 := by
  refine le_trans ?_ hsum
  refine Finset.sum_le_sum (fun x _ => ?_)
  calc (p x) ^ 2 = p x * p x := by ring
    _ ≤ p x * 1 := by exact mul_le_mul_of_nonneg_left (hp1 x) (hp x)
    _ = p x := by ring

end

/-! ## The 2-universal hash family -/

/-- A **2-universal hash family** from a finite source `X` to a finite target
`Y`, indexed by a finite nonempty type `I`. The map `family : I → (X → Y)`
enumerates the hash functions; the `two_universal` axiom says that for any two
*distinct* sources, the fraction of indices on which they collide is at most
`1/|Y|` — i.e. drawing `h` uniformly, `Pr_h[h x = h x'] ≤ 1/|Y|`. -/
structure TwoUniversalHashFamily (X Y : Type*) [Fintype X] [Fintype Y]
    [DecidableEq Y] where
  /-- The index type enumerating the hash functions. -/
  I : Type*
  /-- The index type is finite. -/
  [fintypeI : Fintype I]
  /-- The family is nonempty (there is at least one hash function). -/
  [nonemptyI : Nonempty I]
  /-- The family of hash functions `X → Y`, indexed by `I`. -/
  family : I → (X → Y)
  /-- **2-universality**: for distinct sources `x ≠ x'`, a uniformly random hash
  collides on them with probability at most `1/|Y|`. -/
  two_universal : ∀ x x' : X, x ≠ x' →
    ((Finset.univ.filter (fun i : I => family i x = family i x')).card : ℝ)
      / (Fintype.card I : ℝ) ≤ 1 / (Fintype.card Y : ℝ)

attribute [instance] TwoUniversalHashFamily.fintypeI
attribute [instance] TwoUniversalHashFamily.nonemptyI

noncomputable section

open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-! ## The collision engine of the LHL

For a fixed hash function `f : X → Y`, the hashed variable `f(X)` (push-forward
of `p` along `f`) has probability vector `y ↦ ∑_{x : f x = y} p x`. Its collision
probability is `∑_y (∑_{x : f x = y} p x)²`. The LHL controls the *average* of
this quantity over a uniform choice of `f` from a 2-universal family. -/

/-- The collision probability of the pushed-forward distribution `f(X)`:
`∑_y (∑_{x : f x = y} p x)²`. -/
def pushCollision (f : X → Y) (p : X → ℝ) : ℝ :=
  ∑ y, (∑ x ∈ Finset.univ.filter (fun x => f x = y), p x) ^ 2

/-- **Per-index collision identity.** The collision probability of `f(X)`
re-expands as a double sum of products of `p`-masses over colliding source pairs:
`∑_y (∑_{x : f x = y} p x)² = ∑_x ∑_{x'} [f x' = f x] · p x · p x'`. This is the
algebraic heart that lets the 2-universal axiom act pairwise. -/
theorem pushCollision_eq (f : X → Y) (p : X → ℝ) :
    pushCollision f p =
      ∑ x, ∑ x', (if f x' = f x then p x * p x' else 0) := by
  unfold pushCollision
  have key : ∀ y, (∑ x ∈ Finset.univ.filter (fun x => f x = y), p x) ^ 2
      = ∑ x ∈ Finset.univ.filter (fun x => f x = y),
          ∑ x' ∈ Finset.univ.filter (fun x' => f x' = f x), p x * p x' := by
    intro y
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mem_filter] at hx
    rw [hx.2]
  simp_rw [key]
  rw [Finset.sum_fiberwise (g := f)
    (f := fun x => ∑ x' ∈ Finset.univ.filter (fun x' => f x' = f x), p x * p x')]
  simp_rw [Finset.sum_filter]

end

/-! ## Expected collision over a 2-universal family -/

noncomputable section

open Finset

/-- The **expected collision probability** of `H(X)` when the hash `H` is drawn
uniformly from a 2-universal family `F`: `(1/|I|) · ∑_i pushCollision (F.family i) p`. -/
def expectedCollision {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (F : TwoUniversalHashFamily X Y) (p : X → ℝ) : ℝ :=
  (1 / (Fintype.card F.I : ℝ)) * ∑ i, pushCollision (F.family i) p

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- Swap-and-count: the sum over the family of the per-index collision double-sum
equals a `p`-weighted sum of collision counts over source pairs. -/
private theorem sum_pushCollision_eq_count (F : TwoUniversalHashFamily X Y)
    (p : X → ℝ) :
    (∑ i, pushCollision (F.family i) p)
      = ∑ x, ∑ x', p x * p x'
          * ((Finset.univ.filter (fun i => F.family i x' = F.family i x)).card : ℝ) := by
  simp_rw [pushCollision_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The engine of the Leftover Hash Lemma.** For a probability vector `p`
(`0 ≤ p`, `∑ p = 1`) and a 2-universal family to `Y`, the *expected* collision
probability of the hashed variable `H(X)` is at most `collisionProb p + 1/|Y|`.

This is the genuine cryptographic content: 2-universality forces the off-diagonal
collision mass below the uniform floor `1/|Y|`, while the diagonal reproduces the
source collision probability. -/
theorem expectedCollision_le (F : TwoUniversalHashFamily X Y)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    expectedCollision F p ≤ collisionProb p + 1 / (Fintype.card Y : ℝ) := by
  classical
  have hIpos : 0 < (Fintype.card F.I : ℝ) := by
    have : 0 < Fintype.card F.I := Fintype.card_pos
    exact_mod_cast this
  have hXne : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Finset.univ_eq_empty] at hsum
  have hYne : Nonempty Y :=
    Nonempty.intro (F.family (Classical.arbitrary F.I) (Classical.arbitrary X))
  have hYpos : 0 < (Fintype.card Y : ℝ) := by
    have : 0 < Fintype.card Y := Fintype.card_pos
    exact_mod_cast this
  unfold expectedCollision collisionProb
  rw [sum_pushCollision_eq_count, Finset.mul_sum]
  have step1 : ∀ x, (1 / (Fintype.card F.I : ℝ))
      * ∑ x', p x * p x'
          * ((Finset.univ.filter (fun i => F.family i x' = F.family i x)).card : ℝ)
      = ∑ x', (1 / (Fintype.card F.I : ℝ))
          * (p x * p x'
            * ((Finset.univ.filter (fun i => F.family i x' = F.family i x)).card : ℝ)) := by
    intro x; rw [Finset.mul_sum]
  simp_rw [step1]
  have term_bound : ∀ x x', (1 / (Fintype.card F.I : ℝ))
      * (p x * p x'
        * ((Finset.univ.filter (fun i => F.family i x' = F.family i x)).card : ℝ))
      ≤ (if x = x' then (p x) ^ 2 else 0) + p x * p x' / (Fintype.card Y : ℝ) := by
    intro x x'
    have hpp : 0 ≤ p x * p x' := mul_nonneg (hp x) (hp x')
    by_cases hxx : x = x'
    · subst hxx
      have hfilt :
          (Finset.univ.filter (fun i => F.family i x = F.family i x)) = Finset.univ := by
        apply Finset.filter_true_of_mem; intro i _; rfl
      rw [ite_eq_left rfl, hfilt, Finset.card_univ]
      have heq : (1 / (Fintype.card F.I : ℝ)) * (p x * p x * (Fintype.card F.I : ℝ))
          = p x ^ 2 := by
        have hne : (Fintype.card F.I : ℝ) ≠ 0 := ne_of_gt hIpos
        field_simp
      rw [heq]
      have : 0 ≤ p x * p x / (Fintype.card Y : ℝ) := by positivity
      linarith
    · rw [ite_eq_right hxx, zero_add]
      have hcount :
          ((Finset.univ.filter (fun i => F.family i x' = F.family i x)).card : ℝ)
            / (Fintype.card F.I : ℝ) ≤ 1 / (Fintype.card Y : ℝ) := by
        have := F.two_universal x' x (fun h => hxx h.symm)
        simpa using this
      have key : (1 / (Fintype.card F.I : ℝ))
          * (p x * p x'
            * ((Finset.univ.filter (fun i => F.family i x' = F.family i x)).card : ℝ))
          = p x * p x'
            * (((Finset.univ.filter (fun i => F.family i x' = F.family i x)).card : ℝ)
              / (Fintype.card F.I : ℝ)) := by ring
      rw [key, div_eq_mul_one_div (p x * p x')]
      exact mul_le_mul_of_nonneg_left hcount hpp
  refine le_trans
    (Finset.sum_le_sum (fun x _ =>
      Finset.sum_le_sum (fun x' _ => term_bound x x'))) ?_
  have hdistrib :
      (∑ x, ∑ x',
        ((if x = x' then (p x) ^ 2 else 0) + p x * p x' / (Fintype.card Y : ℝ)))
        = (∑ x, (p x) ^ 2) + 1 / (Fintype.card Y : ℝ) := by
    have hd :
        (∑ x, ∑ x',
          ((if x = x' then (p x) ^ 2 else 0) + p x * p x' / (Fintype.card Y : ℝ)))
          = (∑ x, ∑ x', (if x = x' then (p x) ^ 2 else 0))
            + (∑ x, ∑ x', p x * p x' / (Fintype.card Y : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_add_distrib]
    rw [hd]
    congr 1
    · refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_ite_eq Finset.univ x (fun _ => (p x) ^ 2)]
      simp
    · have hstep : (∑ x, ∑ x', p x * p x' / (Fintype.card Y : ℝ))
          = (∑ x, p x) * (∑ x', p x') / (Fintype.card Y : ℝ) := by
        rw [Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum, Finset.sum_div]
      rw [hstep, hsum]; ring
  rw [hdistrib]

end

/-! ## Statistical distance and the full Leftover Hash Lemma -/

noncomputable section

open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- The pushed-forward (image) probability of `y` under hash `f`:
`pushVec f p y = ∑_{x : f x = y} p x`. Then `pushCollision f p = ∑_y (pushVec f p y)²`. -/
def pushVec (f : X → Y) (p : X → ℝ) (y : Y) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x

/-- `pushCollision` is the sum of squares of the image probabilities. -/
theorem pushCollision_eq_pushVec (f : X → Y) (p : X → ℝ) :
    pushCollision f p = ∑ y, (pushVec f p y) ^ 2 := rfl

/-- The image probabilities sum to the total mass of `p`. -/
theorem sum_pushVec (f : X → Y) (p : X → ℝ) :
    ∑ y, pushVec f p y = ∑ x, p x := by
  unfold pushVec
  rw [Finset.sum_fiberwise (g := f) (f := p)]

/-- The **joint deviation** at `(i, y)` of the real distribution `(h, h(X))` from
the ideal `(h, U_Y)`, drawing `h = family i` uniformly: the real joint mass is
`(1/|I|) · pushVec (family i) p y` and the ideal is `1/(|I|·|Y|)`. -/
def jointDev (F : TwoUniversalHashFamily X Y) (p : X → ℝ) (i : F.I) (y : Y) : ℝ :=
  (1 / (Fintype.card F.I : ℝ)) * pushVec (F.family i) p y
    - 1 / ((Fintype.card F.I : ℝ) * (Fintype.card Y : ℝ))

/-- **Statistical distance** of `(h, h(X))` from `(h, U_Y)`: the `ℓ¹`/total-
variation distance `½ ∑_{i,y} |jointDev|` over the joint outcome. -/
def hashStatDist (F : TwoUniversalHashFamily X Y) (p : X → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ y, |jointDev F p i y|

/-- **L² (collision) identity.** The squared `ℓ²` deviation of the joint
distribution decomposes through the expected collision probability:
`∑_{i,y} jointDev² = (1/|I|) · (E_h[collision] − 1/|Y|)`. -/
theorem sum_jointDev_sq (F : TwoUniversalHashFamily X Y) (p : X → ℝ)
    (hsum : ∑ x, p x = 1) (hIpos : 0 < (Fintype.card F.I : ℝ))
    (hYpos : 0 < (Fintype.card Y : ℝ)) :
    (∑ i, ∑ y, (jointDev F p i y) ^ 2)
      = (1 / (Fintype.card F.I : ℝ))
          * (expectedCollision F p - 1 / (Fintype.card Y : ℝ)) := by
  have hIne : (Fintype.card F.I : ℝ) ≠ 0 := ne_of_gt hIpos
  have hYne : (Fintype.card Y : ℝ) ≠ 0 := ne_of_gt hYpos
  have hq : ∀ i, ∑ y, pushVec (F.family i) p y = 1 := by
    intro i; rw [sum_pushVec]; exact hsum
  have perIndex : ∀ i, (∑ y, (jointDev F p i y) ^ 2)
      = (1 / (Fintype.card F.I : ℝ)) ^ 2
          * ((∑ y, (pushVec (F.family i) p y) ^ 2) - 1 / (Fintype.card Y : ℝ)) := by
    intro i
    unfold jointDev
    have factor : ∀ y, ((1 / (Fintype.card F.I : ℝ)) * pushVec (F.family i) p y
        - 1 / ((Fintype.card F.I : ℝ) * (Fintype.card Y : ℝ))) ^ 2
      = (1 / (Fintype.card F.I : ℝ)) ^ 2
          * (pushVec (F.family i) p y - 1 / (Fintype.card Y : ℝ)) ^ 2 := by
      intro y; field_simp
    simp_rw [factor]
    rw [← Finset.mul_sum]
    congr 1
    have expand : ∀ y, (pushVec (F.family i) p y - 1 / (Fintype.card Y : ℝ)) ^ 2
        = (pushVec (F.family i) p y) ^ 2
          - 2 * (1 / (Fintype.card Y : ℝ)) * pushVec (F.family i) p y
          + (1 / (Fintype.card Y : ℝ)) ^ 2 := by
      intro y; ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hq i]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp; ring
  simp_rw [perIndex]
  rw [← Finset.mul_sum]
  unfold expectedCollision
  simp_rw [pushCollision_eq_pushVec]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **The (classical) Leftover Hash Lemma.** For a probability vector `p`
(`0 ≤ p`, `∑ p = 1`) and a 2-universal hash family to `Y`, the statistical
distance of `(h, h(X))` from the ideal `(h, U_Y)` — over a uniform choice of
`h` — is bounded by

  `δ ≤ ½ · √(|Y| · collisionProb p)`.

Since `collisionProb p = 2^{-H₂(p)}`, this is the familiar
`½ · 2^{-(H₂(p) − log₂|Y|)/2}`. The proof combines the collision engine
(`expectedCollision_le`) with the Cauchy–Schwarz inequality
`sq_sum_le_card_mul_sum_sq` over the joint index set `I × Y`. -/
theorem leftover_hash_lemma (F : TwoUniversalHashFamily X Y)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    hashStatDist F p ≤ (1 / 2) * Real.sqrt ((Fintype.card Y : ℝ) * collisionProb p) := by
  classical
  have hIpos : 0 < (Fintype.card F.I : ℝ) := by
    have : 0 < Fintype.card F.I := Fintype.card_pos
    exact_mod_cast this
  have hXne : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Finset.univ_eq_empty] at hsum
  have hYne : Nonempty Y :=
    Nonempty.intro (F.family (Classical.arbitrary F.I) (Classical.arbitrary X))
  have hYpos : 0 < (Fintype.card Y : ℝ) := by
    have : 0 < Fintype.card Y := Fintype.card_pos
    exact_mod_cast this
  have hcollnn : 0 ≤ collisionProb p := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  -- L² bound via the engine
  have hL2bound : (∑ i, ∑ y, (jointDev F p i y) ^ 2)
      ≤ (1 / (Fintype.card F.I : ℝ)) * collisionProb p := by
    rw [sum_jointDev_sq F p hsum hIpos hYpos]
    have hEng := expectedCollision_le F p hp hsum
    have : expectedCollision F p - 1 / (Fintype.card Y : ℝ) ≤ collisionProb p := by linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  -- Cauchy–Schwarz over the joint index I × Y
  have hcard : (Fintype.card (F.I × Y) : ℝ)
      = (Fintype.card F.I : ℝ) * (Fintype.card Y : ℝ) := by
    rw [Fintype.card_prod]; push_cast; ring
  have hsumeq : (∑ z : F.I × Y, |jointDev F p z.1 z.2|)
      = ∑ i, ∑ y, |jointDev F p i y| := by
    rw [← Finset.sum_product']; rfl
  have hsumeq2 : (∑ z : F.I × Y, (jointDev F p z.1 z.2) ^ 2)
      = ∑ i, ∑ y, (jointDev F p i y) ^ 2 := by
    rw [← Finset.sum_product']; rfl
  have hcs : (∑ z : F.I × Y, |jointDev F p z.1 z.2|)
      ≤ Real.sqrt ((Fintype.card (F.I × Y) : ℝ)
          * ∑ z : F.I × Y, (jointDev F p z.1 z.2) ^ 2) := by
    have hsq : (∑ z : F.I × Y, |jointDev F p z.1 z.2|) ^ 2
        ≤ (Fintype.card (F.I × Y) : ℝ) * ∑ z : F.I × Y, (jointDev F p z.1 z.2) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (F.I × Y)))
        (f := fun z => |jointDev F p z.1 z.2|)
      simp only [sq_abs, Finset.card_univ] at this
      exact this
    have hnn : 0 ≤ ∑ z : F.I × Y, |jointDev F p z.1 z.2| :=
      Finset.sum_nonneg (fun z _ => abs_nonneg _)
    calc ∑ z : F.I × Y, |jointDev F p z.1 z.2|
        = Real.sqrt ((∑ z : F.I × Y, |jointDev F p z.1 z.2|) ^ 2) := by
          rw [Real.sqrt_sq hnn]
      _ ≤ _ := Real.sqrt_le_sqrt hsq
  rw [hsumeq, hsumeq2, hcard] at hcs
  have hinner : (Fintype.card F.I : ℝ) * (Fintype.card Y : ℝ)
        * (∑ i, ∑ y, (jointDev F p i y) ^ 2)
      ≤ (Fintype.card Y : ℝ) * collisionProb p := by
    have h1 : (Fintype.card F.I : ℝ) * (Fintype.card Y : ℝ)
          * (∑ i, ∑ y, (jointDev F p i y) ^ 2)
        ≤ (Fintype.card F.I : ℝ) * (Fintype.card Y : ℝ)
          * ((1 / (Fintype.card F.I : ℝ)) * collisionProb p) :=
      mul_le_mul_of_nonneg_left hL2bound (by positivity)
    refine le_trans h1 (le_of_eq ?_)
    have hIne : (Fintype.card F.I : ℝ) ≠ 0 := ne_of_gt hIpos
    field_simp
  have hfinal : Real.sqrt ((Fintype.card F.I : ℝ) * (Fintype.card Y : ℝ)
        * (∑ i, ∑ y, (jointDev F p i y) ^ 2))
      ≤ Real.sqrt ((Fintype.card Y : ℝ) * collisionProb p) := Real.sqrt_le_sqrt hinner
  unfold hashStatDist
  have hchain : (∑ i, ∑ y, |jointDev F p i y|)
      ≤ Real.sqrt ((Fintype.card Y : ℝ) * collisionProb p) := le_trans hcs hfinal
  linarith [hchain]

end

end Quantum
