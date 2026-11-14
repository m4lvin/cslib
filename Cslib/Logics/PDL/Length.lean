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

/-- The usual length of a PDL formula. -/
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

/-- The usual length of a PDL program. -/
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

set_option linter.auxLemma false in
/-- An alternative way, trying to avoid the duplication? -/
def length' : Formula Label Atom ⊕ Program Label Atom → Nat
-- formula cases:
| .inl (.atom _) => 1
| .inl .false => 0
| .inl (.not φ) => length' (.inl φ) + 1
| .inl (.or φ₁ φ₂) => length' (.inl φ₁) + length' (.inl φ₂) + 1
| .inl (.triangle op φs) => length' (.inr ⟨op, φs ∘ .inl⟩) + length' (.inl (φs (.inr ()))) + 1
-- program cases:
| .inr ⟨.action _, _⟩ => 1
| .inr ⟨.test, tests⟩ => length' (.inl (tests ())) + 1
| .inr ⟨.seq s₁ s₂, tests⟩ =>
    length' (.inr ⟨s₁, tests ∘ .inl⟩) + length' (.inr ⟨s₂, tests ∘ .inr⟩) + 1
| .inr ⟨.union s₁ s₂, tests⟩ =>
    length' (.inr ⟨s₁, tests ∘ .inl⟩) + length' (.inr ⟨s₂, tests ∘ .inr⟩) + 1
| .inr ⟨.star s, tests⟩ => length' (.inr ⟨s, tests⟩) + 1
termination_by
  x =>
    match x with
    | .inl φ => sizeOf φ
    | .inr a => sizeOf a.shape
decreasing_by
  all_goals try grind
  · unfold sizeOf Proposition._sizeOf_inst
    simp only
    unfold Proposition._sizeOf_1
    simp
    -- seems unprovable, probably `0` comes from `sizeOf` ignoring an argument?
    sorry
  · sorry
  · sorry

noncomputable def Formula.length' : Formula Label Atom → Nat
  | φ => Cslib.Logic.Modal.PDL.length' (.inl φ)

noncomputable def Program.length' : Program Label Atom → Nat
  | a => Cslib.Logic.Modal.PDL.length' (.inr a)

end Cslib.Logic.Modal.PDL
