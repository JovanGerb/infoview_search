/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

import Mathlib.Order.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Insert
import InfoviewSearchTest.TestTactic

/-!
This file tests some basic features of `#infoview_search`
-/

set_option linter.hashCommand false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.privateModule false

open scoped InfoviewSearch.Test

#infoview_search
-- set_option infoview_search.debug true

axiom test_sorry {α : Sort*} : α

variable (n m k : Nat)

example (h : 0 + n = n) : n = n + 0 := by
  search_test "/1" =>
    "rw [show n + 0 = n from rfl]"
    "rw [Nat.add_zero]"
  search_test "" =>
    "rfl"
    "rw [Nat.left_eq_add]"
    "refine Nat.dvd_antisymm ?_ ?_"
  search_test h "" => "apply Nat.le.intro at h" "rw [← Nat.beq_eq] at h"
  search_test h "/0/1" => "rw [Nat.add_comm] at h"
  rfl

example : n - 3 ≤ m - 3 := by
  search_test "" => "refine Nat.sub_le_sub_right ?_ 3"
  exact test_sorry

example {α} [LinearOrder α] (a b : α) (h : a ≤ b) (h' : b ≤ a) : a ≤ b := by
  search_test "" => "exact h"
  search_test "/1" => "grw [← h]"
  search_test "/0/1" => "grw [h]"
  apply le_of_lt
  search_test "/1" => "grw [← h]"
  search_test "/0/1" => "grw [h]"
  search_test h "/1" => "grw [h'] at h"
  exact test_sorry

example {α} [LinearOrder α] (a b : α) (h : a < b) (h' : b < a) : a ≤ b := by
  search_test "/1" => "grw [← h]"
  search_test "/0/1" => "grw [h]"
  apply le_of_lt
  search_test "" => "exact h"
  search_test "/1" => "grw [← h]"
  search_test "/0/1" => "grw [h]"
  search_test h "/1" => "grw [h'] at h"
  exact h

example (h : m ≡ k [MOD n]) (h' : m ≡ k + 1 [MOD n]) (h'' : m = k + 1) : m ≡ k [MOD n] := by
  search_test "" => "exact h"
  search_test "/1" => "grw [← h]"
  search_test h' "/0/1" => "grw [h] at h'"
  search_test h' "/0/1" => "rw [h''] at h'"
  exact test_sorry

example {p q r : Prop} (h₁ : p → q → r) (h₂ : p → q) (h₃ : p) : r := by
  search_test h₃ "" => "apply h₂ at h₃"
  -- TODO: support `apply_rw`:
  -- search_test h₁ "/1/0" => "apply_rw [← h₂]"
  exact test_sorry

-- Test with bound variables:
example : ∀ n m : Nat, n + m = m + n := by
  search_test "/1/1/1" => "simp_rw [Nat.add_comm]"
  intro n m
  -- The arguments are only inserted when needed:
  search_test "/1" => "rw [Nat.add_comm m n]"
  search_test "/0/1" => "rw [Nat.add_comm]"
  exact test_sorry

example {α} [Lattice α] [AddGroup α] (f : ℕ → α) (c : α)
    (h : ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| ≤ ε) :
    ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| < ε := by
  intro ε hε n
  obtain ⟨N, hN, h⟩ := h ε hε n
  search_test "/1/1/1/1/1/1" => "grw [← h]"
  exact test_sorry

example {α} [Lattice α] [AddGroup α] (f : ℕ → α) (c : α)
    (h : ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| < ε) :
    ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| ≤ ε := by
  intro ε hε n
  obtain ⟨N, hN, h⟩ := h ε hε n
  search_test "/1/1/1/1/1/1" => "grw [← h]"
  exact test_sorry

example (s t : Set α) (h : s ⊆ t) (h' : t ⊂ s) : s ⊆ t ∪ s := by
  search_test "/0/1" => "nth_grw 1 [h]"
  search_test "/1/0/1" => "grw [← h]"
  search_test "" => "intro x h₁"
  exact test_sorry

namespace AntiSymmRelTest

variable {α : Type u} [Preorder α] {a b c : α}

local infix:50 " ≈ " => AntisymmRel (· ≤ ·)

axiom f : α → α

@[gcongr]
axiom f_congr' : a ≤ b → f a ≤ f b

example (h : a ≈ b) (h' : b ≈ c) : f a ≤ f c := by
  search_test "/0/1/1" => "grw [h]"
  grw [h]
  search_test "/0/1/1" => "grw [← h]" "grw [h']"
  grw [h']

end AntiSymmRelTest

-- test for over-applications
example (f g : Nat → Nat) : (f + g) 2 = f 2 + g 2 := by
  search_test "/0/1" => "rw [add_comm]"
  search_test "/0/1/0" => "rw [add_comm]"
  rw [add_comm]
  search_test "/1" =>
    "rw [Nat.add_comm]"
    "rw [add_comm (f 2) (g 2)]"
  exact test_sorry

-- test for motive not type correct issue
example (a b : Nat) (l : List Nat) (hl : a + b < l.length) (h : l[a + b] = 5) :
    l[b + a] = 5 := by
  search_test "/0/1/0/1" => "rw! [Nat.add_comm]" "rw! [add_comm]"
  rw! [Nat.add_comm]
  exact h

example (a b : Nat) (l : List Nat) (hl : a + b < l.length) (h : l[a + b] = 5) :
    b + a + l[b + a] = b + a + 5 := by
  search_test "/0/1/1/0/1" =>
    "rw! (occs := .pos [2]) [Nat.add_comm b a]"
    "rw! (occs := .pos [2]) [add_comm b a]"
  rw! (occs := .pos [2])  [Nat.add_comm b a]
  rw [h]

lemma Nat.my_inj (n m : Nat) (h : n.succ = m.succ) : n = m := Nat.succ.inj h

-- test which lemmas are and aren't filtered out:
example (n m : Nat) (h : n.succ = m.succ) : True := by
  search_test h "" =>
    "rw [Nat.succ_inj] at h" "rw [Nat.succ.injEq] at h" "apply Nat.my_inj at h"
  -- we do not suggest the automatically generated `.inj` lemma,
  -- because the `.injEq` version is stronger.
  fail_if_success
    search_test h "" => "apply Nat.succ.inj at h  "
  trivial

-- test the `rfl` and `intro` suggestions
example {α} (s : Set α) : s ⊆ s := by
  search_test "" => "intro x h" "rfl"
  rfl

-- test `push` and `push_neg`
example (a b c : α) (s : Set α) (h : a ∈ insert b s) : True := by
  search_test h "" => "simp at h" "push _ ∈ _ at h"
  trivial

-- suggest `+distrib` when it is relevant
example (p q r : Prop) (h : ¬ (p ∧ q)) (h' : ¬ (p ∨ q)) : True := by
  search_test h "" => "push_neg at h" "push_neg +distrib at h"
  search_test h' "" => "push_neg at h'"
  fail_if_success search_test h' "" => "push_neg +distrib at h'"
  trivial

-- test `norm_cast` and `push_cast`
example (a b c : Nat) : (↑(a + b) : Int) * c = ↑(a * c) + (b * c) := by
  search_test "" => "norm_cast" "push_cast" "dsimp" "ring_nf"
  push_cast
  search_test "" =>
    "ring_nf" "norm_cast"
    "exact Int.add_mul ↑a ↑b ↑c" "exact add_mul ↑a ↑b ↑c"
  fail_if_success search_test "" => "push_cast"
  norm_cast
  search_test "" =>
    "ring_nf" "exact Nat.add_mul a b c" "exact add_mul a b c"
  ring_nf

-- test norm_num
example : (2 : ℚ) = 1 + 1 := by
  search_test "" => "norm_num" "norm_cast" "ring_nf"
  norm_num


/-
TODO: add tests for

- You can rewrite with local theorems even if they are a very general match
  (and test that this doesn't work with global theorems).
- The `rw` suggestions only show one of the two directions for lemmas that are the same in
  both directions.
- When it tries to pass arguments explicitly, and this gives an incorrectly located rewrite.
- Test for deduplication logic:
  - numerals in different types are considered different.
  - when instances are different (but defeq), these are considered the same

TODO:

- improve the blacklist heuristic. We should be allowed to use `.inj` and `.injEq`.
  Note: there are theorems with `Simproc` in the name, which should be excluded.
- Allow a user-defined filter in addition to the blacklist?
- improve `nth_rw` heuristic & add a test. Maybe, there should be a `set_option` that determines
  whether to print arguments explicitly.
- The filterdetails should each be focused in the relevant section

- More tactic suggestions
  - `simp`/`dsimp`. This requires integrating with `conv` mode,
    in order to be able to simplify only subterms.
  - `contrapose(!)`/`absurd(!)` on hypothesis and `by_contra(!)` on goal?
  - `push_neg`, `norm_cast`, `push_cast`, `ring_nf`, `field_simp`
  - `cases`/`induction`/`rcases`/`subst`
  - `ext`, `funext`
  - `congr!`, `gcongr`
  - `infer_instance`
  - `rintro`, as a combination of `intro` and `cases`
  - `by_cases` on the selected proposition, if it is not purely in RHS of `→` or either side of `∧`
  - `specialize`/`use`?
  -
- Improve messages of tactic suggestions.
  - `intro` should show the new hypotheses and goal
  - `induction` should somehow show what the induction looks like.
    Then we can also give multiple different `induction`/`cases` suggestions.
- The tactics section should be extensible via an attribute.

- Improve the pasting feature: independent of where the cursor is, we want to paste the
  tactic in the correct place.
  This could also include special-casing for
  - the `by` token (i.e. when creating the first tactic in a sequence)
  - the focus dot `· `
  - being inside another tactic combinator, e.g. `induction`, `cases`, `on_goal`

- Detect whether we are in `conv` mode. I don't know how to. Though the suggestions seem to
  work just fine in conv mode

-/
