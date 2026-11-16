/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger
-/

import Cslib.Logics.PDL.Semantics
import Cslib.Logics.Modal.LogicalEquivalence

namespace CslibTests

open Cslib Logic Modal PDL Model Proposition Satisfies
open scoped InferenceSystem

example (a : Program Nat Nat) (φ : Formula Nat Nat) :
  d⟨a⟩φ = diamond a φ := rfl

example (a : Program Nat Nat) (φ : Formula Nat Nat) :
  d[a]φ = box a φ := rfl

local instance : Coe ℕ (Program ℕ Atom) := ⟨fun k => action k⟩

example :
  let ψ (p q : Nat) (a : Nat) : Formula Nat Nat := d⟨ (?' p ;' a)*⟩ q
  diamond (star (seq (test (.atom 0)) (action 0))) (.atom 1) = ψ 0 1 0 := rfl

/-- ⟨?' ⊥ ∪ ?' ⊤⟩ ⊤ is valid on standard models. -/
theorem test_check_example (m : PDL.Model State Label Atom)
    (h : m.IsStandard) (s : State) :
    ⇓PDL[ m, s ⊨ d⟨?' ⊥ ∪ ?' ⊤⟩ ⊤ ] := by
  -- TODO make and tag enough `grind` lemmas to solve this automatically?
  refine ⟨fun _ => s, ?_, fun _ => fun h => h⟩
  change m.lts.Tr s (?' ⊥ ∪ ?' ⊤) s
  rw [h.regular.union]
  exact .inr ((h.test _ _ _).2 ⟨rfl, fun h => h⟩)


namespace Square

def a : Program Bool Nat := action true
def b : Program Bool Nat := action false

/-- A standard model with 4 states, 2 atomic programs and `Nat` atoms. -/
def squarem : PDL.Model (Fin 4) (Bool) Nat := Model.fromLTS ⟨rel⟩ val where
  /-- The `a = true` program goes up, `b = false` goes down. -/
  rel : Fin 4 → Bool → Fin 4 → Prop
    | x, .true, y => y = x + 1
    | x, .false, y => y = x - 1
  /-- 0,1,2,3 true at one world each, everything ≥4 false. -/
  val w p := w.val = p

theorem squarem_no_reach_four : ⇓PDL[squarem, 0 ⊨ d[a*]¬(.atom 4)] := by
  rw [@pdl_dynBox_iff_forall]
  intro s' reach_s'
  simp only [squarem]
  -- NOTE: maybe have a simp lemma for the atom truth in any `fromLTS` model?
  -- In general, how to ensure that any grind/simp lemma applicable to
  -- regular frames and standard models also gets used for `fromLTS`?
  rw [Satisfies.pdl_not_iff_not, Satisfies.pdl_atom_iff]
  unfold fromLTS LTS.toRegular squarem.val
  cases s'
  grind

theorem squarem_forward_backward {w φ} : ⇓PDL[squarem, w ⊨ φ → d[(a;'b)*]φ] := by
  rw [@pdl_imp_iff_imp]
  intro w_φ
  rw [@pdl_dynBox_iff_forall]
  intro s w_s
  convert w_φ -- remains to show s = w
  simp only [squarem] at w_s
  have := Model.fromLTS_IsStandard ⟨squarem.rel⟩ squarem.val
  rw [this.regular.star] at w_s
  simp_rw [this.regular.seq a b] at w_s
  -- unsure what's elegant here.
  unfold a b at w_s
  unfold fromLTS LTS.toRegular squarem.val at w_s
  unfold squarem.rel at w_s
  simp [] at w_s
  sorry

end Square

namespace NatModel

/-- `Nat` as a PDL Model with one atomic program. -/
def natm : PDL.Model Nat Unit Nat := Model.fromLTS ⟨rel⟩  val where
  rel := fun w1 () w2 => w2 = w1.succ
  val w p := w = p

@[simp]
lemma natm_models_iff_eq : ⇓PDL[natm, w ⊨ atom n] ↔ w = n := by
  rw [@pdl_atom_iff]
  simp [natm, fromLTS, natm.val]

abbrev a : Program Unit Nat := action ()

theorem natm_zero_sat_dia_unit_one :
    ⇓PDL[natm, 0 ⊨ d[a](.atom 1) ] := by
  -- grind[modal]
  rw [pdl_dynBox_iff_forall]
  intro s' s'zero_a_s'
  rw [pdl_atom_iff]
  -- NOTE: what lemmas would make this proof less "hands on" and easier?
  simp only [natm, fromLTS, natm.val] at *
  change s' = 0 + 1
  simp only [LTS.toRegular, a, action, Shape.rel] at s'zero_a_s'
  exact s'zero_a_s'

theorem natm_zero_dia_any_nat {n : Nat} :
    ⇓PDL[natm, 0 ⊨ d⟨a*⟩(.atom n) ] := by
  have := Model.fromLTS_IsStandard ⟨natm.rel⟩ natm.val
  induction n
  · -- this really should be a one line grind from here?
    rw [pdl_dynDiamond_iff_exists]
    refine ⟨0, ?_, ?_⟩
    · -- TODO: simp lemma `whatever.lts.Tr 0 a* 0` for regular models
      unfold natm
      rw [this.regular.star]
    · simp
  case succ n IH =>
    rw [pdl_dynDiamond_iff_exists]
    refine ⟨n+1, ?_, ?_⟩
    · simp only [pdl_dynDiamond_iff_exists, natm_models_iff_eq, exists_eq_right] at IH
      rw [natm, this.regular.star] at IH
      rw [natm, this.regular.star]
      apply Relation.ReflTransGen.tail IH
      simp [LTS.toRegular, a, action, Shape.rel, fromLTS, natm.rel]
    · simp

end NatModel

end CslibTests
