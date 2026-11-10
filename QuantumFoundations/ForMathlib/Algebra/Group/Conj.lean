/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import Mathlib.Algebra.Group.Defs

/-!
# Conjugation by involutions
-/

public section

/-- Multiplying conjugates cancels the interior copies of an involution. -/
theorem conj_mul_conj_of_involution {M : Type*} [Monoid M] (C : M) (hC : C * C = 1) (P Q : M) :
    (C * P * C) * (C * Q * C) = C * (P * Q) * C := by
  calc
    _ = C * P * (C * C) * Q * C := by simp only [mul_assoc]
    _ = _ := by rw [hC, mul_one]; simp only [mul_assoc]

/-- Conjugation by an involution preserves commutation. -/
theorem conj_comm_of_involution {M : Type*} [Monoid M] {P A B : M} (hP : P * P = 1)
    (h : A * B = B * A) : P * A * P * (P * B * P) = P * B * P * (P * A * P) := by
  rw [conj_mul_conj_of_involution P hP, conj_mul_conj_of_involution P hP, h]
