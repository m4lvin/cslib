/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger, Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.PFunctor.Basic
public import Cslib.Foundations.Logic.Operators
public import Cslib.Logics.Modal.Basic

/-! # Syntax of Propositional Dynamic Logic (PDL)

PDL is about the behaviour of programs and originates from [FischerLadner1979].
It extends Hennessy-Milner Logic from `Cslib.Logics.HML.Basic` with a `test`
operator and three ways to combine programs: `seq`, `union` and `star`.

`Formula` and `Program` are defined as a mutual inductive.  Programs are also viewed as
a `Shape` plus a map from its test positions to formulas, which gives the modal signature
used by `Cslib.Logic.Modal.Proposition`.  The correspondence between the two views is an
equivalence, `Formula.equivProposition`.

NOTES:

- The `Cslib.Logic.Modal.Proposition.nabla` should *not* be used for `Formula` here,
  because via `PropositionMap.not` it negates the formulas at *all* argument positions.
  Then `[?p]q` would become `¬⟨?¬p⟩¬q` whereas we want it to be `¬⟨?p⟩¬q`, where the
  formula in the test position is not negated but stays as it is.

  Instead, we define our own box operator in `Cslib.Logic.Modal.PDL.box`.

## References

* [Michael J. Fischer and Richard E. Ladner,
  *Propositional Dynamic Logic of Regular Programs*][FischerLadner1979]
* [D. Harel, D. Kozen and J. Tiuryn, *Dynamic Logic*][HarelKozenTiuryn2000]
* [E. Koole, *Extending Interpolation to PDL with Frame Conditions*][Koole2026]
* The code is also inspired by [lean4-pdl](https://github.com/m4lvin/lean4-pdl).

-/

@[expose] public section

namespace Cslib.Logic.Modal.PDL

universe u v

/-! ## Syntax -/

/-- The shape of a PDL program, where test formulas are not yet provided. -/
inductive Shape (Label : Type u) where
  | action (name : Label)
  | test
  | seq (a b : Shape Label)
  | union (a b : Shape Label)
  | star (a : Shape Label)
  deriving DecidableEq, Repr

/-- As many copies of `Unit` as there are tests in the given `Shape`. -/
abbrev Tests {Label : Type u} : Shape Label → Type
  | .action _ => Empty
  | .test => Unit
  | .seq a b => Tests a ⊕ Tests b
  | .union a b => Tests a ⊕ Tests b
  | .star a => Tests a

/-- The modal signature for PDL. -/
abbrev signature (Label : Type u) : PFunctor :=
  ⟨Shape Label, fun a => Tests a ⊕ Unit⟩

mutual
/-- Formulas of Propositional Dynamic Logic. -/
inductive Formula (Label : Type u) (Atom : Type v) where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsehood. -/
  | false
  /-- Negation. -/
  | not (φ : Formula Label Atom)
  /-- Disjunction. -/
  | or (φ₁ φ₂ : Formula Label Atom)
  /-- Diamond modality: after some execution of `a`, `φ` holds. -/
  | diamond (a : Program Label Atom) (φ : Formula Label Atom)

/-- A PDL program. -/
inductive Program (Label : Type u) (Atom : Type v) where
  /-- Atomic program. -/
  | action (name : Label)
  /-- Test program. -/
  | test (ψ : Formula Label Atom)
  /-- Sequential composition of programs. -/
  | seq (a b : Program Label Atom)
  /-- Non-deterministic choice between two programs. -/
  | union (a b : Program Label Atom)
  /-- Kleene star to iterate a program any number of times (including 0). -/
  | star (a : Program Label Atom)
end

variable {Label : Type u} {Atom : Type v}

/-- An atomic program. -/
abbrev action (name : Label) : Program Label Atom := .action name

/-- Test program. -/
abbrev test (ψ : Formula Label Atom) : Program Label Atom := .test ψ

/-- Sequential composition of programs. -/
abbrev seq (a b : Program Label Atom) : Program Label Atom := .seq a b

/-- Non-deterministic choice between two programs. -/
abbrev union (a b : Program Label Atom) : Program Label Atom := .union a b

/-- Kleene star to iterate a program any number of times (including 0). -/
abbrev star (a : Program Label Atom) : Program Label Atom := .star a

/-- The shape of a program, forgetting its test formulas. -/
def Program.shape (a : Program Label Atom) : Shape Label :=
  match a with
  | .action n => .action n
  | .test _ => .test
  | .seq a b => .seq a.shape b.shape
  | .union a b => .union a.shape b.shape
  | .star a => .star a.shape

/-- The test formulas of a program, one for each `Shape.test` placeholder. -/
def Program.tests (a : Program Label Atom) : Tests a.shape → Formula Label Atom :=
  match a with
  | .action _ => Empty.elim
  | .test ψ => fun _ => ψ
  | .seq a b => Sum.elim a.tests b.tests
  | .union a b => Sum.elim a.tests b.tests
  | .star a => a.tests

/-! ## Propositional connectives -/

instance : Coe Atom (Formula Label Atom) := ⟨.atom⟩
instance : Bot (Formula Label Atom) := ⟨.false⟩
instance : HasNot (Formula Label Atom) := ⟨.not⟩
instance : HasOr (Formula Label Atom) := ⟨.or⟩

/-- Truth. -/
@[match_pattern]
def Formula.true : Formula Label Atom := ¬⊥

instance : Top (Formula Label Atom) := ⟨Formula.true⟩

/-- Conjunction. -/
@[match_pattern]
def Formula.and (φ₁ φ₂ : Formula Label Atom) := ¬(¬φ₁ ∨ ¬φ₂)

instance : HasAnd (Formula Label Atom) := ⟨Formula.and⟩

/-- Implication. -/
@[match_pattern]
def Formula.imp (φ₁ φ₂ : Formula Label Atom) := ¬φ₁ ∨ φ₂

instance : HasImp (Formula Label Atom) := ⟨Formula.imp⟩

/-- Bi-implication. -/
@[match_pattern]
def Formula.iff (φ₁ φ₂ : Formula Label Atom) := (φ₁ → φ₂) ∧ (φ₂ → φ₁)

instance : HasIff (Formula Label Atom) := ⟨Formula.iff⟩

@[scoped grind =]
lemma Formula.true_def : Formula.true (Label := Label) (Atom := Atom) = ⊤ := rfl

@[scoped grind =]
lemma Formula.and_def (φ₁ φ₂ : Formula Label Atom) : φ₁.and φ₂ = (φ₁ ∧ φ₂) := rfl

@[scoped grind =]
lemma Formula.imp_def (φ₁ φ₂ : Formula Label Atom) : φ₁.imp φ₂ = (φ₁ → φ₂) := rfl

@[scoped grind =]
lemma Formula.iff_def (φ₁ φ₂ : Formula Label Atom) : φ₁.iff φ₂ = (φ₁ ↔ φ₂) := rfl

/-! ## Dynamic modalities -/

/-- PDL diamond modality: after some execution of `a` we reach a state satisfying `φ`. -/
abbrev diamond (a : Program Label Atom) (φ : Formula Label Atom) : Formula Label Atom :=
  .diamond a φ

instance : HasDynamicDiamond (Formula Label Atom) (Program Label Atom) := ⟨diamond⟩

/-- The dual of `diamond`. After any execution of `a` we reach a state satisfying `φ`. -/
def box (a : Program Label Atom) (φ : Formula Label Atom) : Formula Label Atom :=
  ¬ diamond a (¬ φ)

instance : HasDynamicBox (Formula Label Atom) (Program Label Atom) := ⟨box⟩

@[scoped grind =]
theorem diamond_def : diamond a φ = d⟨a⟩φ := rfl

@[scoped grind =]
theorem box_def : box a φ = d[a]φ := rfl

/-! ## Notation -/

/-- Notation for the test operator `Program.test`. -/
scoped notation "?' " ψ:arg => test ψ

/-- Notation for sequential composition `Program.seq`. -/
scoped infixr:70 " ;' " => seq

/-- Notation for non-deterministic choice `Program.union`. -/
instance : Union (Program Label Atom) := ⟨union⟩

/-- Notation for the iteration operator `Program.star`. -/
scoped postfix:max "*" => star

/-! ## Equivalence with `Modal.Proposition`

`Modal.Proposition (signature Label) Atom` represents a program by its shape and a map
from the test positions to propositions.  We translate between the two representations and
show that they are inverses. -/

/-- Rebuild a program from a shape and its test formulas. -/
def Program.fromShape : (s : Shape Label) → (Tests s → Formula Label Atom) → Program Label Atom
  | .action n, _ => .action n
  | .test, ts => .test (ts ())
  | .seq s t, ts => .seq (fromShape s (ts ∘ Sum.inl)) (fromShape t (ts ∘ Sum.inr))
  | .union s t, ts => .union (fromShape s (ts ∘ Sum.inl)) (fromShape t (ts ∘ Sum.inr))
  | .star s, ts => .star (fromShape s ts)

mutual
/-- View a formula as a modal proposition over the PDL signature. -/
def Formula.toProposition (φ : Formula Label Atom) : Proposition (signature Label) Atom :=
  match φ with
  | .atom p => .atom p
  | .false => .false
  | .not φ => .not φ.toProposition
  | .or φ ψ => .or φ.toProposition ψ.toProposition
  | .diamond a φ =>
    let ⟨s, ts⟩ := Program.toPropositionTests a
    .triangle s (Sum.elim ts (fun _ => φ.toProposition))

/-- The shape and test propositions of a program. -/
def Program.toPropositionTests (a : Program Label Atom) :
    Sigma (fun s : Shape Label => Tests s → Proposition (signature Label) Atom) :=
  match a with
  | .action n => ⟨.action n, Empty.elim⟩
  | .test ψ => ⟨.test, fun _ => ψ.toProposition⟩
  | .seq a b =>
    let ⟨sa, ta⟩ := a.toPropositionTests
    let ⟨sb, tb⟩ := b.toPropositionTests
    ⟨.seq sa sb, Sum.elim ta tb⟩
  | .union a b =>
    let ⟨sa, ta⟩ := a.toPropositionTests
    let ⟨sb, tb⟩ := b.toPropositionTests
    ⟨.union sa sb, Sum.elim ta tb⟩
  | .star a =>
    let ⟨sa, ta⟩ := a.toPropositionTests
    ⟨.star sa, ta⟩
end

/-- Translate a `Modal.Proposition` over the PDL signature back into a PDL formula. -/
def Formula.ofProposition (ψ : Proposition (signature Label) Atom) : Formula Label Atom :=
  match ψ with
  | .atom p => .atom p
  | .false => .false
  | .not φ => .not (Formula.ofProposition φ)
  | .or φ ψ => .or (Formula.ofProposition φ) (Formula.ofProposition ψ)
  | .triangle s φs =>
    .diamond (Program.fromShape s (fun t => Formula.ofProposition (φs (.inl t))))
      (Formula.ofProposition (φs (.inr ())))

/-- Translating a program to modal propositions and back gives the original program. -/
theorem Program.toPropositionTests_fromShape (s : Shape Label) (ts : Tests s → Formula Label Atom) :
    Program.toPropositionTests (Program.fromShape s ts) =
      ⟨s, fun t => (ts t).toProposition⟩ := by
  induction s with
  | action n =>
    rw [Program.fromShape, Program.toPropositionTests]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext t
      exact t.elim
  | test =>
    rw [Program.fromShape, Program.toPropositionTests]
  | seq s t ihs iht =>
    rw [Program.fromShape]
    simp only [Program.toPropositionTests]
    rw [ihs (ts ∘ Sum.inl), iht (ts ∘ Sum.inr)]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext i
      cases i <;> rfl
  | union s t ihs iht =>
    rw [Program.fromShape]
    simp only [Program.toPropositionTests]
    rw [ihs (ts ∘ Sum.inl), iht (ts ∘ Sum.inr)]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext i
      cases i <;> rfl
  | star s ihs =>
    rw [Program.fromShape]
    have h := ihs (show Tests s → Formula Label Atom from ts)
    simpa only [Program.toPropositionTests] using
      congrArg (fun p : Sigma (fun s' : Shape Label =>
        Tests s' → Proposition (signature Label) Atom) =>
        (⟨Shape.star p.fst, p.snd⟩ : Sigma (fun s' : Shape Label =>
          Tests s' → Proposition (signature Label) Atom))) h

@[simp]
theorem Formula.ofProposition_toProposition (φ : Formula Label Atom) :
    Formula.ofProposition φ.toProposition = φ := by
  refine Formula.rec
    (motive_1 := fun φ => Formula.ofProposition φ.toProposition = φ)
    (motive_2 := fun a =>
      Program.fromShape (Program.toPropositionTests a).1
        (fun t => Formula.ofProposition ((Program.toPropositionTests a).2 t)) = a)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ φ
  · intro p; rfl
  · rfl
  · intro φ ih; rw [Formula.toProposition, Formula.ofProposition, ih]
  · intro φ ψ ihφ ihψ; rw [Formula.toProposition, Formula.ofProposition, ihφ, ihψ]
  · intro a φ iha ihφ
    rw [Formula.toProposition, Formula.ofProposition]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [iha, ihφ]
  · intro n; rfl
  · intro ψ ih
    rw [Program.toPropositionTests, Program.fromShape, ih]
  · intro a b iha ihb
    rw [Program.toPropositionTests, Program.fromShape]
    apply congrArg₂ Program.seq
    · change Program.fromShape (Program.toPropositionTests a).1
          (fun t => Formula.ofProposition ((Program.toPropositionTests a).2 t)) = a
      exact iha
    · change Program.fromShape (Program.toPropositionTests b).1
          (fun t => Formula.ofProposition ((Program.toPropositionTests b).2 t)) = b
      exact ihb
  · intro a b iha ihb
    rw [Program.toPropositionTests, Program.fromShape]
    apply congrArg₂ Program.union
    · change Program.fromShape (Program.toPropositionTests a).1
          (fun t => Formula.ofProposition ((Program.toPropositionTests a).2 t)) = a
      exact iha
    · change Program.fromShape (Program.toPropositionTests b).1
          (fun t => Formula.ofProposition ((Program.toPropositionTests b).2 t)) = b
      exact ihb
  · intro a iha
    simp only [Program.toPropositionTests, Program.fromShape]
    exact congrArg Program.star iha

@[simp]
theorem Formula.toProposition_ofProposition (ψ : Proposition (signature Label) Atom) :
    Formula.toProposition (Formula.ofProposition ψ) = ψ := by
  induction ψ with
  | atom p => rfl
  | false => rfl
  | not φ ih => rw [Formula.ofProposition, Formula.toProposition, ih]
  | or φ ψ ihφ ihψ => rw [Formula.ofProposition, Formula.toProposition, ihφ, ihψ]
  | triangle s φs ih =>
    rw [Formula.ofProposition, Formula.toProposition]
    rw [Program.toPropositionTests_fromShape]
    simp only
    apply congrArg (Proposition.triangle s)
    funext i
    cases i with
    | inl t => exact ih (.inl t)
    | inr u => exact ih (.inr u)

/-- PDL formulas are equivalent to modal propositions over the PDL signature. -/
def Formula.equivProposition : Formula Label Atom ≃ Proposition (signature Label) Atom where
  toFun := Formula.toProposition
  invFun := Formula.ofProposition
  left_inv := Formula.ofProposition_toProposition
  right_inv := Formula.toProposition_ofProposition

/-! ## Induction Principles

`Formula` and `Program` are a mutual inductive, so their recursors already take one motive
for each type.  The names `Formula.induction` and `Program.induction` keep the established
API: both take the same ten hypotheses and can be used via
`induction φ using Formula.induction (motive_2 := ...)` and
`induction a using Program.induction (motive_1 := ...)`, respectively. -/

/-- Induction principle for PDL formulas, with a second motive for programs. -/
@[elab_as_elim]
noncomputable def Formula.induction := @Formula.rec

/-- Induction principle for PDL programs, with a second motive for formulas. -/
@[elab_as_elim]
noncomputable def Program.induction := @Program.rec

end Cslib.Logic.Modal.PDL
