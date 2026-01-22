module

import Mathlib.Order.Basic
import Mathlib.Data.Nat.ModEq
import InfoviewSearchTest.Defs

/-!
This file tests some basic features of `#infoview_suggest`
-/

set_option linter.hashCommand false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.privateModule false

open scoped InfoviewSearch.Test

#infoview_search

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
  search_test h "/1" => "grw [h'] at h\n  "
  exact test_sorry

example (h : m ≡ k [MOD n]) (h' : m ≡ k + 1 [MOD n]) : m ≡ k [MOD n] := by
  search_test "" => "exact h\n  "
  search_test "/1" => "grw [← h]\n  "
  -- TODO: make this work:
  -- search_test h "/1" => "grw [← h'] at h\n  "
  exact test_sorry
