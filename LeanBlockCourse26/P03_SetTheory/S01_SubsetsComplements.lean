/-
This section is mostly inspired by the Set Theory Game:
https://github.com/leanprover-community/lean4game
-/

import Mathlib.Data.Set.Basic
import ProofGolf

/-
Let us review something that we already briefly used in the last exercise block:

So far we have always seen variables as explicit arguments to statements, usually
looking something like `(P : Prop)`. Here we are doing three things differently:

1. We are using `variable` to declare a variable that is used in any statement that follows.
2. We are using curly brackets `{}` to denote an implicit argument.
3. We are using `Type*` to denote an unspecified type (more on this later).
-/

-- So far we have specified all arguments explicitly ...
theorem explicit_argument (P : Prop) (p : P) : P := p

-- ... but in this case specifying `p : P` already implies `P : Prop`.
theorem implicit_argument {P : Prop} (p : P) : P := p

/--
Both of these state the same, but specifying `{P : Prop}` reduces the number of arguments
you need to specify when invoking it.
-/
example (R S : Prop) (r : R) (s : S) : R ∧ S := by
  constructor
  · exact explicit_argument R r
  · exact implicit_argument s

-- Note that you can always override any implicit arguments with `@`
example (R S : Prop) (r : R) (s : S) : R ∧ S := by
  constructor
  · exact @implicit_argument R r  -- now we *need* to specify the `R` ...
  · exact @implicit_argument _ s  -- ... though you can refuse to elaborate through `_`

/-
Using `variable` allows us to have cleaner theorem statements whenever arguments are
shared. Other languages also have global variables but usually these are very much
discouraged. In Lean however they are very important and used throughout mathlib:
if you are working on a file that collects statements about finite simple graphs,
you do not want to specify for each that it requires to be given a
simple graph `(G : SimpleGraph V)` with implicit vertex type `{V : Type*}` which
is also finite `[FinType V]` (the square brackets we will elaborate on later).

We can scope these shared arguments through a `namespace`.
-/

namespace sharedArgumentExample

variable {P : Prop} (R S : Prop)

theorem implicit_argument' (p : P) : P := p

example (r : R) (s : S) : R ∧ S := by
  constructor
  · exact implicit_argument' r
  · exact implicit_argument' s

example (r : R) (s : S) : R ∧ S := by
  constructor
  · exact @implicit_argument' R r
  · exact @implicit_argument' _ s

end sharedArgumentExample

-- Because the `namespace` was closed, this no longer knows about `{P : Prop}`
example {P : Prop} (p : P) : P := p

-- To access results from a `namespace` you need to re-open it or explicitly specify it.
-- #check implicit_argument'                    -- This does *not* work ...
#check sharedArgumentExample.implicit_argument' -- ... but this does!

/-
# Sets
=====================

`S : Set α` means `S` is a set of elements of type `α`.

Note that all of the named statements in this section are already in mathlib
in the namespace `Set` which one can access by either preceding the name with `Set.`
or by opening the namespace with `open Set`.
-/

variable {α : Type*}

/-
A `Set` in mathlib is just a predicate `α → Prop`.

```
def Set (α : Type u) := α → Prop
```

Importantly it:

(i)  Needs an underlying type `α` that all set elements are instances of
(ii) Is defined through a predicate `α → Prop` with `e : α` an element of `S` iff `P e`

Notation like `{ ... }`, `∈`, `∉`, `⊆`, `∅`, ... are nice syntactic sugar on top of this.
But note that mathlib actually does *not* want you to think of sets like this:

"Although `Set` is defined as `α → Prop`, this is an implementation detail which should
not be relied on. Instead, `setOf` and membership of a set (`∈`) should be used to
convert between sets and predicates."
-/

-- `x ∈ S` is notation for `Membership x S` and `{x | P x}` for `setOf P`
lemma mem_setOf (x₀ : α) (P : α → Prop) : x₀ ∈ { x | P x} ↔ P x₀ := by rfl

-- example (x₀ : α) (P : α → Prop) : Membership x₀ (setOf P) ↔ P x₀ := rfl

-- `Nonempty S` means the type `S` is not empty, which can be proven with `use`...
example (x : α) (S : Set α) (h : x ∈ S) : Nonempty S := by
  use x

-- ... or directly through term mode
example (x : α) (S : Set α) (h : x ∈ S) : Nonempty S := ⟨x, h⟩

-- `{x}` constructs the set containing `x`
lemma mem_singleton_iff {x y : α} : x ∈ ({y} : Set α) ↔ x = y :=  by rfl

-- Both sides are definitionally equal (`x ∈ ({y} : Set α)` unfolds to `x = y`),
-- so the `rfl` tactic closes this via `Iff.rfl`. Term mode `rfl` only proves
-- `a = a`, not `a ↔ a`, so it does not work directly.
example {x y : α} : x ∈ ({y} : Set α) ↔ x = y := by
  apply Iff.intro <;> intro h <;> exact h

-- The `: Set α` annotation disambiguates `{y}` from other set-like types (e.g. `Finset`);
-- `Set.singleton y` is an unambiguous alternative that does not need it
example {x y : α} : x ∈ Set.singleton y ↔ x = y := by rfl

-- `{x, y}` constructs the set containing two elements `x` and `y`
lemma mem_pair (t x y : α) : t ∈ ({x, y} : Set α) ↔ t = x ∨ t = y := by rfl

/-
`S ⊆ T` is syntax for `HasSubset` and is (essentially) defined as
`∀ x, x ∈ S → x ∈ T`. `S ⊂ T` is syntax for `HasSSubset` and is
(again essentially) defined as `S ⊆ T ∧ ¬T ⊆ S`.
-/

-- This is `Set.subset_def` in mathlib
lemma subset_def {S T : Set α} : (S ⊆ T) = ∀ x ∈ S, x ∈ T := rfl

-- This is `Set.ssubset_def` in mathlib
lemma ssubset_def {S T : Set α} : (S ⊂ T) = (S ⊆ T ∧ ¬T ⊆ S) := rfl

/-
## Set Reflexivity

Every set is a subset of itself — `Set.Subset.rfl` in mathlib.
-/

lemma Subset.rfl (S : Set α) : S ⊆ S := by rfl

example (S : Set α) : S ⊆ S := by
  rw [subset_def] -- You can rewrite definitions, but here this is optional
  intro x h
  exact h

/-
## Set Transitivity

If `S ⊆ T` and `T ⊆ R` then `S ⊆ R` — `Set.Subset.trans` in mathlib.
-/

lemma Subset.trans {S T R : Set α} (h₁ : S ⊆ T) (h₂ : T ⊆ R) : S ⊆ R := by
  rw [subset_def] at * -- again optional
  intro x (xs : x ∈ S)
  have xt : x ∈ T := h₁ x xs
  have xr : x ∈ R := h₂ x xt
  exact xr

example {S T R : Set α} (h₁ : S ⊆ T) (h₂ : T ⊆ R) : S ⊆ R := by
  intro x (xs : x ∈ S)
  have xt : x ∈ T := h₁ xs -- if we do not rewrite then `x` is implicit here ...
  have xr : x ∈ R := h₂ xt -- ... and here
  exact xr

example {S T R : Set α} (h₁ : S ⊆ T) (h₂ : T ⊆ R) : S ⊆ R := fun _ xs => h₂ (h₁ xs)

/-
## Empty Set

The empty set `∅` is the set of elements of type `α` for which `False` holds
(`Set.empty_def` in mathlib), and is a subset of every set (`Set.empty_subset`).
-/

theorem empty_def : ∅ = {x : α | False} := rfl

-- The empty set is a subset of every set — `Set.empty_subset` in mathlib
lemma empty_subset (S : Set α) : ∅ ⊆ S := by
  rw [empty_def, subset_def]
  intro x h
  exfalso
  rw [mem_setOf] at h
  exact h

example (S : Set α) : ∅ ⊆ S := by
  intro x h
  exfalso
  exact h

-- this does not use any axioms though, just `False.elim`
#golf example (S : Set α) : ∅ ⊆ S := by
  intro x h
  contradiction

/-
## Exercise Block B01

Try to find compact term mode proofs whenever possible.
-/

namespace P03S01B01

variable {S T : Set α}

-- Exercise 1.1
example {x : α} (h₁ : S ⊆ T) (h₂ : x ∈ S) : x ∈ T := by
  sorry

-- Exercise 1.2
example {x : α} (R : Set α) (h₁ : S ⊆ T) (h₂ : T ⊆ R) (h₃ : x ∈ S) : x ∈ R :=
 sorry

-- Exercise 1.3
example {x : α} {R : Set α} (h₁ : S ⊆ T) (h₂ : x ∈ T → x ∈ R) : x ∈ S → x ∈ R := by
  sorry

-- Exercise 1.4
example (h : S ⊆ T) {x : α} (hx : x ∉ T) : x ∉ S := by
  sorry

-- Exercise 1.5 (Master)
example {R : Set α} (h₁ : S ⊂ T) (h₂ : T ⊆ R) : S ⊂ R := by
  sorry

-- Exercise 1.6 (Master)
example : ∃ U, U ⊆ S := by
  sorry

end P03S01B01
