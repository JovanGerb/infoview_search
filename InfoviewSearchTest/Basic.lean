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
import Mathlib.Data.Finset.Max
import Mathlib.SetTheory.ZFC.Basic

/-!
This file tests some basic features of `#infoview_search`
-/

set_option linter.all false

open scoped InfoviewSearch.Test

#infoview_search
set_option infoview_search.debug true

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
  -- TODO: this shouldn't show up
  search_test "" =>
    "rw [Nat.Simproc.eq_add_gt]"
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
  -- TODO: this should be suggested:
  fail_if_success search_test "/1/1/1/1/1/1" => "grw [hε]"
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
  search_test "" => "intro a h₁"
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

-- Test for over-applications
example (f g : Nat → Nat) : (f + g) 2 = f 2 + g 2 := by
  search_test "/0/1" => "rw [add_comm]"
  search_test "/0/1/0" => "rw [add_comm]"
  rw [add_comm]
  search_test "/1" =>
    "rw [Nat.add_comm]"
    "rw [add_comm (f 2) (g 2)]"
  exact test_sorry

-- Test for motive not type correct issue
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

-- Test which lemmas are and aren't filtered out:
example (n m : Nat) (h : n.succ = m.succ) : True := by
  search_test h "" =>
    "rw [Nat.succ_inj] at h" "rw [Nat.succ.injEq] at h" "apply Nat.my_inj at h"
  -- we do not suggest the automatically generated `.inj` lemma,
  -- because the `.injEq` version is stronger.
  fail_if_success
    search_test h "" => "apply Nat.succ.inj at h  "
  trivial

-- Test the `rfl` and `intro` suggestions
example {α} (s : Set α) : s ⊆ s := by
  search_test "" => "intro a h" "rfl"
  rfl

-- The names of the introduced variables are modified to not overlap existing names.
example {α} (s : Set α) (a h : 1 = 2) : s ⊆ s := by
  search_test "" => "intro a₁ h₁" "rfl"
  rfl

-- We're happy to overwrite global constants
example : ∀ Nat : Nat, Nat = Nat := by
  search_test "" => "intro Nat"
  intro Nat
  rfl

-- We prefer `by_contra` over `intro` when possible
example (p : Prop) (h : ¬ p) : ¬ p := by
  search_test => "by_contra h₁"
  fail_if_success search_test => "intro h₁"
  -- TODO:
  -- search_test "h" => "contrapose h"
  exact h

-- Test `push` and `push_neg`
example (a b c : α) (s : Set α) (h : a ∈ insert b s) : True := by
  search_test h "" => "simp at h" "push _ ∈ _ at h"
  trivial

-- Suggest `+distrib` when it is relevant
example (p q r : Prop) (h : ¬ (p ∧ q)) (h' : ¬ (p ∨ q)) : True := by
  search_test h "" => "push_neg at h" "push_neg +distrib at h"
  search_test h' "" => "push_neg at h'"
  fail_if_success search_test h' "" => "push_neg +distrib at h'"
  trivial

-- Test `norm_cast` and `push_cast`
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

-- Test norm_num
example : (2 : ℚ) = 1 + 1 := by
  search_test "" => "norm_num" "norm_cast" "ring_nf"
  norm_num

-- test `ring`
example {α} [CommRing α] (a b : α) : Odd a → Odd b → Odd (a * b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨2 * a * b + b + a, ?_⟩
  search_test "" => "ring_nf"
  fail_if_success search_test "" => "noncomm_ring"
  ring_nf

example {α} [Ring α] (a b : α) : Odd a → Odd b → Odd (a * b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨2 * a * b + b + a, ?_⟩
  search_test "" => "noncomm_ring"
  noncomm_ring
  congr 2
  -- TODO: this only changes the `2 : ℤ` into `2 : ℕ`. Should this somehow be made clearer?
  search_test "" => "norm_cast"
  exact test_sorry

-- Test induction
example {p : Nat → Prop} (n) : p n := by
  search_test n =>
    "induction n"
    "induction n using Nat.strongRec"
    "induction n using Nat.binaryRec"
    "cases n"
  exact test_sorry

example {p : Int → Prop} (z) : p z := by
  search_test z =>
    "induction z"
    "induction z using Int.negInduction"
    "cases z"
  exact test_sorry

example {p : Finset Int → Prop} (s) : p s := by
  search_test s => "induction s using Finset.induction"
  exact test_sorry

example {p : ZFSet → Prop} (s) : p s := by
  search_test s => "induction s using ZFSet.inductionOn"
  exact test_sorry

example {p : Nat → Prop} (n) : p n := by
  search_test "/1" =>
    "induction n"
    "induction n using Nat.strongRec"
    "induction n using Nat.binaryRec"
    "cases n"
  exact test_sorry
/-
TODO for the induction suggestions:
- make induction using `Quotient.induction_on_pi` work.
- deduplication when multiple recursors do the same thing.
- paste the whole induction tactic including all match arms.
- use `rcases` instead of `cases` for non-case-splitting `cases`.
- that also unlocks the possibility for `rintro` rather than intro
- `rcases h with rfl` can simply be replaced by `subst h`
-/

-- Test that projections aren't reduced in the discrimination tree indexing:
example (n : Nat) : n = n := by
  fail_if_success search_test "" => "exact String.Pos.Raw.byteIdx_mk n"
  search_test "" => "exact rfl"
  rfl

-- And hence, it is possible to suggest `Fin.val_mk` in the right scenario:
example (n m : Nat) (h : n < m) : Fin.val ⟨n, h⟩ = n := by
  search_test "/0/1" => "rw [Fin.val_mk]"
    "conv =>\n enter [1]\n dsimp only"
    "push_cast" -- Recall `push_cast` has no `conv` mode version.
  rw [Fin.val_mk]

-- TODO: pattern `a = b` vs `a = a`
-- TODO: `CancelDenoms.derive_trans` namespace

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

- Note: there are theorems with `Simproc` in the name, which should be excluded.
- Allow a user-defined filter in addition to the blacklist?
- improve `nth_rw` heuristic & add a test. Maybe, there should be a `set_option` that determines
  whether to print arguments explicitly.

- More tactic suggestions
  - `contrapose(!)`/`absurd(!)` on hypothesis and `by_contra(!)` on goal?
  - `ext`, `funext`
  - `congr!`, `gcongr`
  - `infer_instance`, `decide`
  - `by_cases` on the selected proposition, if it is not purely in RHS of `→` or either side of `∧`
  - `specialize`/`use`?
  - `fun_induction`/`fun_cases`?
- The tactics section should be extensible via an attribute.

- Improve the pasting feature: independent of where the cursor is, we want to paste the
  tactic in the correct place.
  This could also include special-casing for
  - the `by` token (i.e. when creating the first tactic in a sequence)
  - the focus dot `· `
  - being inside another tactic combinator, e.g. `induction`, `cases`, `on_goal`

- Detect whether we are in `conv` mode, by detecting the mdata. Though the suggestions seem to
  work mostly fine in conv mode already.

-/
