/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under MIT or Apache 2.0 license as described in the files LICENSE-MIT and LICENSE-APACHE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.Register
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Data.Fintype.Prod

/-!
# Subsystems of a register

A subsystem is a factorization of a register into a selected register and its complement.
-/

public section

namespace Quantum

/-- A subsystem `A` of the register `M`: a register `rest`, the complement of `A`, and a
factorization `equiv : M ≃ A × rest` of the basis of `M`. -/
structure Subsystem (A M : QReg) where
  /-- The complement of the subsystem. -/
  rest : QReg
  /-- The factorization of the basis of `M` into the subsystem and its complement. -/
  equiv : M ≃ A × rest

namespace Subsystem

variable {A B M : QReg}

/-- The whole register as a subsystem of itself, with a one-dimensional complement. -/
@[expose]
def whole (A : QReg) : Subsystem A A :=
  ⟨QReg.of Unit, (Equiv.prodPUnit A).symm⟩

/-- The left factor of a product register. -/
@[expose]
def fst (A B : QReg) : Subsystem A (QReg.of (A × B)) :=
  ⟨B, Equiv.refl _⟩

/-- The right factor of a product register. -/
@[expose]
def snd (A B : QReg) : Subsystem B (QReg.of (A × B)) :=
  ⟨A, Equiv.prodComm A B⟩

/-- The complement of a subsystem, as a subsystem whose complement is the original one. -/
@[expose]
def complement (S : Subsystem A M) : Subsystem S.rest M :=
  ⟨A, S.equiv.trans (Equiv.prodComm A S.rest)⟩

/-- A subsystem `S` of a subsystem `T` of `M` is a subsystem of `M`, whose complement collects
both complements. -/
@[expose]
def comp (T : Subsystem B M) (S : Subsystem A B) : Subsystem A M :=
  ⟨QReg.of (S.rest × T.rest),
    T.equiv.trans ((S.equiv.prodCongr (Equiv.refl T.rest)).trans
      (Equiv.prodAssoc A S.rest T.rest))⟩

/-- The pair of a subsystem `S` and a subsystem `T` of its complement: the two are disjoint by
construction, and together form the subsystem `A × B`. -/
@[expose]
def pair (S : Subsystem A M) (T : Subsystem B S.rest) : Subsystem (QReg.of (A × B)) M :=
  ⟨T.rest, S.equiv.trans (((Equiv.refl A).prodCongr T.equiv).trans
    (Equiv.prodAssoc A B T.rest).symm)⟩

/-- The whole register pairs each basis element with the unit. -/
@[simp]
theorem whole_equiv_apply (a : A) : (whole A).equiv a = (a, ()) :=
  rfl

/-- The left factor of a product is factored by the identity. -/
@[simp]
theorem fst_equiv_apply (x : A × B) : (fst A B).equiv x = x :=
  rfl

/-- The right factor of a product is factored by the swap. -/
@[simp]
theorem snd_equiv_apply (x : A × B) : (snd A B).equiv x = (x.2, x.1) :=
  rfl

/-- The complement swaps the factorization. -/
@[simp]
theorem complement_equiv_apply (S : Subsystem A M) (m : M) :
    S.complement.equiv m = ((S.equiv m).2, (S.equiv m).1) :=
  rfl

/-- A subsystem of a subsystem factors through both factorizations. -/
@[simp]
theorem comp_equiv_apply (T : Subsystem B M) (S : Subsystem A B) (m : M) :
    (T.comp S).equiv m = ((S.equiv (T.equiv m).1).1, (S.equiv (T.equiv m).1).2, (T.equiv m).2) :=
  rfl

/-- A pair factors through the first subsystem and then its complement. -/
@[simp]
theorem pair_equiv_apply (S : Subsystem A M) (T : Subsystem B S.rest) (m : M) :
    (S.pair T).equiv m = (((S.equiv m).1, (T.equiv (S.equiv m).2).1), (T.equiv (S.equiv m).2).2) :=
  rfl

/-- The complement of the complement factors `M` as the original subsystem does. -/
@[simp]
theorem complement_complement_equiv (S : Subsystem A M) :
    S.complement.complement.equiv = S.equiv :=
  Equiv.ext fun _ ↦ rfl

end Subsystem

end Quantum
