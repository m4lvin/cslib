/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.HML.Basic
import Cslib.Logics.Modal.LogicalEquivalence
import Cslib.Languages.CCS.Semantics

namespace CslibTests

open Cslib Logic Modal HML LTS Model Proposition Satisfies
open scoped InferenceSystem

example [∀ p μ, Finite ((CCS.lts (defs := defs)).image p μ)] :
    TheoryEq (HML.Model.toModal
      ⟨CCS.lts (defs := defs), fun _ (_ : Unit) => True⟩) =
      (· ~[CCS.lts (defs := defs)] ·) := theoryEq_eq_bisimilarity ..

example (m : HML.Model State Label Atom) (htr : m.lts.Tr s μ s')
    (hφ : ⇓HML[m,s' ⊨ φ]) : ⇓HML[m,s ⊨ d⟨μ⟩φ] := by grind only [modal]

example (m : HML.Model State Label Atom) (hbox : ⇓HML[m,s ⊨ d[μ]φ])
    (htr : m.lts.Tr s μ s') : ⇓HML[m,s' ⊨ φ] := by grind only [modal]

section LogicalEquivalence

/-
The next example tests that logical equivalence can lift equivalences.

We prove it twice. Once using our infrastructure for up-to context reasoning directly, and then
with grind. Note that the grind proof works because Satisfies.and_iff_and gives a congruence
principle on the satisfaction relation for the and-connective.
-/

open PFunctor

example {State : Type u} {m : HML.Model State Label Atom} {s : State} {μ : Label}
    {φ₁ φ₂ : HML.Proposition Label Atom} (h : ⇓HML[m,s ⊨ (d⟨μ⟩φ₁) ∧ φ₂]) :
    ⇓HML[m,s ⊨ (¬d[μ]¬φ₁) ∧ φ₂] := by
  let pc : HasContext.Context (HML.Proposition Label Atom) := Context.andL .hole φ₂
  have dual a (φ : HML.Proposition Label Atom) : d⟨a⟩φ ≡[UEquiv (World := State)] ¬d[a]¬φ := by
    grind only [modal, Satisfies.unary_dual]
  have eqv := LawfulCongruence.covariant.elim pc (dual μ φ₁)
  let jc : HasHContext.Context (Judgement State (mkUnary Label) Atom)
      (HML.Proposition Label Atom) := Judgement.Context.mk m.toModal s
  apply LogicalEquivalence.eqvFillValid eqv jc h

example {State : Type u} {m : HML.Model State Label Atom} {s : State} {μ : Label}
    {φ₁ φ₂ : HML.Proposition Label Atom} (h : ⇓HML[m,s ⊨ (d⟨μ⟩φ₁) ∧ φ₂]) :
    ⇓HML[m,s ⊨ (¬d[μ]¬φ₁) ∧ φ₂] := by grind [modal]

end LogicalEquivalence

section SimpMkUnary

variable {State Label Atom : Type*} {m : HML.Model State Label Atom} {s : State}
  {a b : Label} {φ : HML.Proposition Label Atom}

/-! These tests verify that the `no_index` simp lemmas in the general modal
framework (`Cslib.Logics.Modal.Unary.Basic`) apply to concrete `mkUnary`
signatures such as HML, whose action type is `Label` rather than `τ.A`. -/

-- `Satisfies.dynDiamond_iff_exists_no_index` (general framework, not HML-specific)
-- works with `simp` for HML's concrete action type `Label`.
example : ⇓HML[m,s ⊨ d⟨a⟩φ] ↔ ∃ s', m.toModal.toFrame.diagonal a s s' ∧ ⇓HML[m,s' ⊨ φ] := by
  -- simp only [Satisfies.dynDiamond_iff_exists] -- does not work
  simp only [Satisfies.dynDiamond_iff_exists_no_index] -- does work

-- Same for nested diamonds.
example : ⇓HML[m,s ⊨ d⟨a⟩(d⟨b⟩φ)] ↔
    ∃ s', m.toModal.toFrame.diagonal a s s' ∧
      ∃ s'', m.toModal.toFrame.diagonal b s' s'' ∧ ⇓HML[m,s'' ⊨ φ] := by
  simp only [Satisfies.dynDiamond_iff_exists_no_index]

-- With additional HML-specific simp lemmas, `simp` fully expands to `m.lts.Tr` transitions.
example : ⇓HML[m,s ⊨ d⟨a⟩(d⟨b⟩φ)] ↔
    ∃ s', m.lts.Tr s a s' ∧ ∃ s'', m.lts.Tr s' b s'' ∧ ⇓HML[m,s'' ⊨ φ] := by
  simp only [Satisfies.dynDiamond_iff_exists_no_index, HML.Model.toModal_toFrame,
    LTS.toFrame_diagonal_iff_tr]

-- `Satisfies.dynBox_iff_forall_no_index` (general framework) also works for HML.
example : ⇓HML[m,s ⊨ d[a]φ] ↔ ∀ s', m.toModal.toFrame.diagonal a s s' → ⇓HML[m,s' ⊨ φ] := by
  simp only [Satisfies.dynBox_iff_forall_no_index]

-- Nested box-diamond combinations using both general-framework lemmas.
example : ⇓HML[m,s ⊨ d[a](d⟨b⟩φ)] ↔
    ∀ s', m.toModal.toFrame.diagonal a s s' →
      ∃ s'', m.toModal.toFrame.diagonal b s' s'' ∧ ⇓HML[m,s'' ⊨ φ] := by
  simp only [Satisfies.dynBox_iff_forall_no_index, Satisfies.dynDiamond_iff_exists_no_index]

end SimpMkUnary

end CslibTests
