/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger
-/

module

public import Cslib.Logics.HML.Basic

/-! # `simp` ignores generic `d⟨·⟩` lemmas for concrete `mkUnary` signatures

For HML (and PDL), whose signature is `PFunctor.mkUnary Label`, `simp` does not use
`Satisfies.dynDiamond_iff_exists`, while `rw` does. For an abstract `τ` with `[τ.Unary]` it works.

Cause: elaborating `d⟨a⟩φ` with `a : Label` puts `Label` as the action type of
`HasDynamicDiamond.dynDiamond`, but the generic lemma has `τ.A` there. `simp`'s discrimination
tree indexes this implicit argument, and `?τ.A` does not match `Label`, so the lemma is never tried.
The same happens for the other generic `d⟨·⟩`/`d[·]` lemmas, e.g. `@[simp] dynDiamond_eq_triangle`.

Proposed fix: state these lemmas with `no_index (d⟨a⟩φ)`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open HML
open scoped InferenceSystem

variable {State Label Atom : Type*} {m : HML.Model State Label Atom} {s : State}
  {a b : Label} {φ : HML.Proposition Label Atom}

/-- `simp` makes no progress, `rw` works. -/
example : ⇓HML[m,s ⊨ d⟨a⟩φ] ↔ ∃ s', m.lts.toFrame.diagonal a s s' ∧ ⇓HML[m,s' ⊨ φ] := by
  fail_if_success simp only [Satisfies.dynDiamond_iff_exists]
  rw [Satisfies.dynDiamond_iff_exists]
  rfl

/-- Without the discrimination-tree index, `simp` does use the lemma. -/
example : ⇓HML[m,s ⊨ d⟨a⟩φ] ↔ ∃ s', m.lts.toFrame.diagonal a s s' ∧ ⇓HML[m,s' ⊨ φ] := by
  simp (config := { index := false }) only [Satisfies.dynDiamond_iff_exists]
  rfl

/-- For an abstract signature `simp` works, also for nested diamonds. -/
example {World : Type*} {τ : PFunctor} [τ.Unary] {m : Modal.Model World τ Atom} {w : World}
    {a b : τ.A} {φ : Proposition τ Atom} :
    ⇓Modal[m,w ⊨ d⟨a⟩(d⟨b⟩φ)] ↔ ∃ w', m.toFrame.diagonal a w w' ∧
      ∃ w'', m.toFrame.diagonal b w' w'' ∧ ⇓Modal[m,w'' ⊨ φ] := by
  simp only [Satisfies.dynDiamond_iff_exists]

/-- Proposed fix: the generic lemma with `no_index`. -/
theorem Satisfies.dynDiamond_iff_exists_no_index {World : Type*} {τ : PFunctor} [τ.Unary]
    {m : Modal.Model World τ Atom} {w : World} {a : τ.A} {φ : Proposition τ Atom} :
    ⇓Modal[m,w ⊨ no_index (d⟨a⟩φ)] ↔ ∃ w', m.toFrame.diagonal a w w' ∧ ⇓Modal[m,w' ⊨ φ] :=
  Satisfies.dynDiamond_iff_exists

/-- With it, `simp` works for HML, also for nested diamonds. -/
example : ⇓HML[m,s ⊨ d⟨a⟩(d⟨b⟩φ)] ↔
    ∃ s', m.lts.Tr s a s' ∧ ∃ s'', m.lts.Tr s' b s'' ∧ ⇓HML[m,s'' ⊨ φ] := by
  simp only [Satisfies.dynDiamond_iff_exists_no_index, HML.Model.toModal_toFrame,
    LTS.toFrame_diagonal_iff_tr]

end Cslib.Logic.Modal
