/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push
import Mathlib.Tactic.NthRewrite
import ProofGolf

/-
# Negation and Classical Logic
=====================

This module builds on previous logical foundations to explore:

- Working with negation (`¬`) and contradiction
- Classical reasoning with `by_contra`
- Simplifying negations using `push_neg`
- Handling contradictions with `exfalso` and `contradiction`
-/

/-
## Understanding Negation

In Lean, `¬P` is defined as `P → False`. This perspective allows us to:

- Treat negations as implication arrows to `False`
- Use implication-handling tactics with negations
-/

#check Not -- `Not (a : Prop) : Prop`, i.e., `Prop → Prop`

/-
In Lean, `Not` is just constructed as `a → False`, so the only ingredients
needed are the type `Prop : Type` and `False : Prop` and the functional
composition through `→`.

def Not (a : Prop) : Prop := a → False
-/


-- This definition makes `rfl` work here ...
example (P : Prop) : ¬P ↔ (P → False) := by
  rfl

-- ... but we can also be a bit more verbose.
example (P : Prop) : ¬P ↔ (P → False) := by
  constructor
  · intro h  -- `h` states that `P` is not true, that is `P → False`
    intro p  -- `p` states that `P` is true
    exact h p
  · intro h
    exact h

example (P : Prop) : ¬P ↔ (P → False) := by
  constructor
  all_goals intro h; exact h

example (P : Prop) : ¬P ↔ (P → False) := 
  ⟨id, id⟩

-- If you have a negation in the assumption you can sometimes derive `False`
example (P Q : Prop) (h : P → ¬Q) (p : P) (q : Q) : False := by
  obtain h := h p
  exact h q

example (P Q : Prop) (h : P → ¬Q) (p : P) (q : Q) : False :=
  (h p) q

/-
## The `contradiction` Tactic

The `contradiction` tactic automatically closes goals with:

- Direct `False` hypotheses
- Obviously conflicting assumptions
- Mismatched constructors in inductive types

It is used around 400 times in mathlib.
-/

example (P : Prop) (h : False) : P := by
  contradiction

example (P Q : Prop) (h : P) (hn : ¬P) : Q := by
  contradiction

/-
Side remark: assuming `False` or anything that produces `False`, i.e.,
a contradiction in our assumptions, allows us to prove *anything*
(Fermat's last theorem, any open conjecture, obvious falsehoods, ...).

By Gödel we unfortunately know that no magical tactic (meaning an
algorithm) can exist that can verify your assumptions are free of
contradictions, since we provably cannot show that any sufficiently
sophisticated logical system is free of contradiction.
-/

/-
## The `trivial` tactic

`trivial` tries different simple tactics, in particular `contradiction`,
to close the current goal. It is used around 500 times in mathlib.
-/

example (P : Prop) (h : P) : P := by
  trivial

/-
## The `exfalso` tactic

The `exfalso` tactic converts any goal to `False`, allowing you to:

- Work explicitly with contradictions
- Use any false assumption to prove arbitrary claims
- Combine with other tactics for manual contradiction handling

It is used around 200 times in mathlib.
-/

theorem exfalso_example (P : Prop) (h : False) : P := by
  exfalso    -- Changes goal to False
  exact h    -- Uses the False hypothesis

#print exfalso_example  -- Under the hood this uses `False.elim h`

#print axioms exfalso_example -- We are still not using classical logic!

/-
## The `push_neg` Tactic (Classical logic)

Normalizes negated expressions by pushing negation inward:

- Converts `¬(P ∧ Q)` to `P → ¬Q`
- Converts `¬(P → Q)` to `P ∧ ¬Q`
- Converts `¬¬P` to `P` (uses law of excluded middle: `P ∨ ¬P`)
- Simplifies nested negations
-/

theorem push_neg_example (P : Prop) : ¬¬P → P := by
  push_neg
  exact id

#print axioms push_neg_example  -- This does use the axiom of excluded middle (classical logic)

/-
## Exercise Block B01

Related: https://www.youtube.com/watch?v=aMxcAaR0oHU
-/

-- Exercise 1.1a
-- Prove the statement using `push_neg`
theorem nnp_of_p_exercise_push_neg (P : Prop) : P → ¬¬P := by
  intro p
  push_neg
  exact p

#print axioms nnp_of_p_exercise_push_neg

-- Exercise 1.1b
-- Prove the statement without `push_neg` amd without classical
-- logic, i.e., use `#print axioms` to make sure you are not
-- dependent on any (`Classical.`) axioms!
theorem nnp_of_p_exercise_fun (P : Prop) : P → ¬¬P := by
  intro p
  intro np
  exact np p

#print axioms nnp_of_p_exercise_fun

theorem nnp_of_p_exercise_fun_term (P : Prop) : P → ¬¬P := fun p np => np p

#print axioms nnp_of_p_exercise_fun_term

theorem nnp_of_p_exercise_contradiction (P : Prop) : P → ¬¬P := by
  intro p
  intro np
  contradiction

#print axioms nnp_of_p_exercise_contradiction

-- Exercise 1.2
example (P Q : Prop) (p : ¬¬P) (f : P → Q) : ¬¬Q := by
  push_neg
  push_neg at p
  exact f p

example (P Q : Prop) (p : ¬¬P) (f : P → Q) : ¬¬Q := by
  push_neg at *
  exact f p

-- Exercise 1.3
example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  intro _ ⟨⟨p, q⟩, r⟩
  apply h
  · rcases ‹(P ∨ Q) ∨ R› with hpq | r
    · rcases hpq with p | q
      · left; exact p
      · right; left; exact q
    · right; right; exact r
  · exact ⟨p, q, r⟩

example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  rintro ((p | q) | r)
  all_goals
    rintro ⟨⟨p, q⟩, r⟩
  · exact (h (Or.inl p)) ⟨p, q, r⟩
  · exact (h (Or.inl p)) ⟨p, q, r⟩
  · exact (h (Or.inl p)) ⟨p, q, r⟩

#golf example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  rintro ((p | q) | r)
  all_goals
  rintro ⟨⟨p, q⟩, r⟩
  exact (h (Or.inl p)) ⟨p, q, r⟩

#golf example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  rintro ((p | q) | r) <;> rintro ⟨⟨p, q⟩, r⟩ <;> exact (h (Or.inl p)) ⟨p, q, r⟩

#golf example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  push_neg at *
  rintro _ ⟨p, q⟩
  exact h (Or.inl p) p q

-- Exercise 1.4
#golf example (P Q : Prop) (h : P → ¬ Q) (p : P) (q : Q) : False := by
  suffices ¬Q by contradiction
  exact h p

#golf example (P Q : Prop) (h : P → ¬ Q) (p : P) (q : Q) : False := by
  exact h p q
