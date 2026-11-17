/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger
-/

module

public import Cslib.Logics.PDL.Basic

/-! # Fischer-Ladner Closure

TODO: add references

Inspired by `Pdl/FischerLadner.lean` in the `lean4-pdl` project.
-/

@[expose] public section

namespace Cslib.Logic.Modal.PDL

open Modal PDL

variable {State Label Atom : Type*}

/-- The Fischer-Ladner closure of a formula.
See Section 6.1 of [HKT2000]. Note that there only implication is given.
For our `Formula` type we cover discjunction and negation.
Also note that we are closing under single negations as well here.
The main work is done by the second motive which also ensures termination. -/
def FL : Formula Label Atom → Set (Formula Label Atom) :=
  @Formula.induction Label Atom
    (motive_1 := fun _ => Set (Formula Label Atom))
    (motive_2 := fun _ => Formula Label Atom → Set (Formula Label Atom))
    -- formulas:
    (atom := fun p => {.atom p, ¬ .atom p} )
    (false := {.false, ¬ .false} )
    (not := fun φ rec => {¬ φ} ∪ rec)
    (or := fun φ1 φ2 rec1 rec2 => {.or φ1 φ2, .not (.or φ1 φ2), .not φ1, .not φ2} ∪ rec1 ∪ rec2)
        -- do we need .not φ1, .not φ2 in the line above?
    (diamond := fun α φ recα recφ => { d⟨α⟩φ, ¬ d⟨α⟩φ } ∪ recα φ ∪ recφ )
    -- programs (this was `FLb` in the lean4-pdl version):
    (action := fun a φ => { d⟨action a⟩φ, ¬d⟨action a⟩φ })
    (seq := fun α β recα recβ φ => { d⟨α;'β⟩φ, ¬ d⟨α;'β⟩φ } ∪ recα (d⟨β⟩φ) ∪ recβ φ)
    (union := fun α β recα recβ φ => { d⟨α ∪ β⟩φ, ¬ d⟨α ∪ β⟩φ } ∪ recα φ ∪ recβ φ)
    (star := fun α recα φ => { d⟨α*⟩φ, ¬ d⟨α*⟩φ } ∪ recα (d⟨α*⟩φ))
    (test := fun τ recτ φ => { d⟨?'τ⟩φ, ¬ d⟨?'τ⟩φ } ∪ recτ )

end Cslib.Logic.Modal.PDL
