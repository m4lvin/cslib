/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger
-/

module

public import Cslib.Logics.PDL.Basic

/-! # Length of PDL formulas and programs

As an example how the induction principles can be ued, here we
define the syntactic complexity of PDL formulas and programs.

NOTE: In the first approach it seems wrong that we need to define everything twice.

-/

@[expose] public section

namespace Cslib.Logic.Modal.PDL

variable {Label Atom : Type*}

/-- The length of a PDL formula. -/
def Formula.length : Formula Label Atom → Nat :=
  Formula.induction
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (atom := fun _ => 1)
    (false := 0)
    (not := fun _ n => n + 1)
    (or := fun _ _ n m => n + m + 1)
    (diamond := fun _ _ n m => n + m + 1)
    (action := fun _ => 1)
    (test := fun _ n => n + 1)
    (seq := fun _ _ n m => n + m + 1)
    (union := fun _ _ n m => n + m + 1)
    (star := fun _ n => n + 1)

/-- The length of a PDL program. -/
def Program.length : Program Label Atom → Nat :=
  Program.induction
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (atom := fun _ => 1)
    (false := 0)
    (not := fun _ n => n + 1)
    (or := fun _ _ n m => n + m + 1)
    (diamond := fun _ _ n m => n + m + 1)
    (action := fun _ => 1)
    (test := fun _ n => n + 1)
    (seq := fun _ _ n m => n + m + 1)
    (union := fun _ _ n m => n + m + 1)
    (star := fun _ n => n + 1)

/-- An alternative way, avoid the repetition via `parallel_induction`. -/
def length' : Formula Label Atom ⊕ Program Label Atom → Nat :=
  let f := @mutualInduction Label Atom
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (atom := fun _ => 1)
    (false := 0)
    (not := fun _ n => n + 1)
    (or := fun _ _ n m => n + m + 1)
    (diamond := fun _ _ n m => n + m + 1)
    (action := fun _ => 1)
    (test := fun _ n => n + 1)
    (seq := fun _ _ n m => n + m + 1)
    (union := fun _ _ n m => n + m + 1)
    (star := fun _ n => n + 1)
  fun x => match x with
  | .inl φ => f.1 φ
  | .inr a => f.2 a

/-- The length of a PDL formula. -/
def Formula.length' : Formula Label Atom → Nat
  | φ => Cslib.Logic.Modal.PDL.length' (.inl φ)

/-- The length of a PDL program. -/
def Program.length' : Program Label Atom → Nat
  | a => Cslib.Logic.Modal.PDL.length' (.inr a)

end Cslib.Logic.Modal.PDL
