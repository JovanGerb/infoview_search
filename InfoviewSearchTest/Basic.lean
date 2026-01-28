module

import Mathlib.Order.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Basic
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
set_option infoview_search.debug true

axiom test_sorry {α : Sort*} : α

variable (n m k : Nat)

example : n = n + 0 := by
  search_test "/1" =>
    "rw [show n + 0 = n from rfl]\n  "
    "rw [Nat.add_zero]\n  "
  search_test "" =>
    "rfl\n  "
    "rw [Nat.left_eq_add]\n  "
    "refine Nat.dvd_antisymm ?_ ?_\n  "
  rfl

example : n - 3 ≤ m - 3 := by
  search_test "" => "refine Nat.sub_le_sub_right ?_ 3\n  "
  exact test_sorry

example {α} [LinearOrder α] (a b : α) (h : a ≤ b) (h' : b ≤ a) : a ≤ b := by
  search_test "" => "exact h\n  "
  search_test "/1" => "grw [← h]\n  "
  search_test "/0/1" => "grw [h]\n  "
  apply le_of_lt
  search_test "/1" => "grw [← h]\n  "
  search_test "/0/1" => "grw [h]\n  "
  search_test h "/1" => "grw [h'] at h\n  "
  exact test_sorry

example (h : m ≡ k [MOD n]) (h' : m ≡ k + 1 [MOD n]) (h'' : m = k + 1) : m ≡ k [MOD n] := by
  search_test "" => "exact h\n  "
  search_test "/1" => "grw [← h]\n  "
  search_test h' "/0/1" => "grw [h] at h'\n  "
  search_test h' "/0/1" => "rw [h''] at h'\n  "
  exact test_sorry

example {p q r : Prop} (h₁ : p → q → r) (h₂ : p → q) (h₃ : p) : r := by
  search_test h₃ "" => "apply h₂ at h₃\n  "
  -- TODO: support `apply_rw`:
  -- search_test h₁ "/1/0" => "apply_rw [← h₂]\n  "
  exact test_sorry

-- Test with bound variables:
example : ∀ n m : Nat, n + m = m + n := by
  search_test "/1/1/1" => "simp_rw [Nat.add_comm]\n  "
  intro n m
  -- The arguments are only inserted when needed:
  search_test "/1" => "rw [Nat.add_comm m n]\n  "
  search_test "/0/1" => "rw [Nat.add_comm]\n  "
  exact test_sorry

example {α} [Lattice α] [CommRing α] (f : ℕ → α) (c : α)
    (h : ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| ≤ ε) :
    ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| < ε := by
  intro ε hε n
  obtain ⟨N, hN, h⟩ := h ε hε n
  search_test "/1/1/1/1/1/1" => "grw [← h]\n  "
  exact test_sorry

example {α} [Lattice α] [CommRing α] (f : ℕ → α) (c : α)
    (h : ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| < ε) :
    ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| ≤ ε := by
  intro ε hε n
  obtain ⟨N, hN, h⟩ := h ε hε n
  search_test "/1/1/1/1/1/1" => "grw [← h]\n  "
  exact test_sorry

example (s t : Set α) (h : s ⊆ t) (h' : t ⊂ s) : s ⊆ t ∪ s := by
  search_test "/0/1" => "nth_grw 1 [h]\n  "
  search_test "/1/0/1" => "grw [← h]\n  "
  search_test "" => "intro x h₁\n  "
  exact test_sorry

namespace AntiSymmRelTest

variable {α : Type u} [Preorder α] {a b c : α}

local infix:50 " ≈ " => AntisymmRel (· ≤ ·)

axiom f : α → α

@[gcongr]
axiom f_congr' : a ≤ b → f a ≤ f b

example (h : a ≈ b) (h' : b ≈ c) : f a ≤ f c := by
  search_test "/0/1/1" => "grw [h]\n  "
  grw [h]
  search_test "/0/1/1" => "grw [← h]\n  " "grw [h']\n  "
  grw [h']

end AntiSymmRelTest

/-
TODO: add tests for

- You can rewrite with local theorems even if they are a very general match
  (and test that this doesn't work with global theorems).
- The `rw` suggestions only show one of the two directions for lemmas that are the same in
  both directions.
- When it tries to pass arguments explicitly, and this gives an incorrectly located rewrite.

TODO:

- use `rw!` instead of `rw` when motive is not type correct
- improve `nth_rw` heuristic & add a test
- The filterdetails should each be focused in the relevant section

-/
