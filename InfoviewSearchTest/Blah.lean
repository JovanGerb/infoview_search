module

public import Mathlib
public import InfoviewSearch

section
#infoview_search

variable {n : Nat}
namespace Finset


/-- The set that attains the upper bound -/
def maximalSet (n m : Nat) : Finset (Finset (Fin (2 * n))) :=
  powersetCard m univ

-- It is indeed an antichain
theorem IsAntichain_maximalSet : IsAntichain (· ⊆ ·) (SetLike.coe (maximalSet n m)) := by
  intro s hs t ht hst h
  rw [maximalSet] at hs ht
  grind [subset_iff_eq_of_card_le]

-- and it is equal to the upper bound.
theorem ncard_maximalSet : #(maximalSet n n) = (2 * n).choose n := by
  simp [maximalSet]

/-- A `Chain` is a sequence of consecutive elements in `Finset (Fin (2 * n))`
from `n - m` to `n + m`. -/
def Chain (n m : Nat) :=
  { f : Ico (n - m) (n + m) → Finset (Fin (2 * n)) //
    (∀ i, #(f i) = i) ∧ ∀ i j, i ≤ j → f i ⊆ f j }

theorem chain_nonempty {n m : Nat} (h : m ≤ n) : Nonempty (Chain n m) :=
  ⟨fun i ↦ Iio ⟨i, by grind⟩, by simp_rw [Fin.card_Iio]; grind [Fin.lt_def, Subtype.mk_le_mk]⟩



/-- The finset of elements in a chain. -/
def Chain.toFinset {n m : Nat} (chain : Chain n m) : Finset (Finset (Fin (2 * n))) :=
  image chain.val univ

theorem Chain.eq_of_mem_toSet_of_mem_isAntichain (a b : Finset (Fin (2 * n)))
    (A : Set (Finset (Fin (2 * n)))) (hA : IsAntichain (· ⊆ ·) A)
    {m : Nat} (chain : Chain n m)
    (ha : a ∈ A) (hb : b ∈ A) (ha' : a ∈ chain.toFinset) (hb' : b ∈ chain.toFinset) :
    a = b := by
  rw [toFinset, mem_image_univ_iff_mem_range] at ha' hb'
  obtain ⟨ia, rfl⟩ := ha'
  obtain ⟨ib, rfl⟩ := hb'
  wlog hle : ia ≤ ib
  · exact (this A hA chain ib hb ia ha (by lia)).symm
  specialize hA ha hb
  simp at hA
  grind

/-- A chain meets a slice in `Ico (n - m) (n + m)` exactly once. -/
theorem Chain.card_toFinset_inter_powersetCard_eq_one
    {n m : Nat} (chain : Chain n m)
    (k : Nat) (hk : k ∈ Ico (n - m) (n + m)) :
    #(chain.toFinset ∩ powersetCard k univ) = 1 := by
  -- TODO: discr-tree building is insanely slow here
  rw [card_eq_one]
  use chain.1 ⟨k, by grind⟩
  grind [toFinset]

/-- A chain meets a slice at most once. -/
theorem Chain.card_toFinset_inter_powersetCard_le_one
    {n m : Nat} (chain : Chain n m) (k : Nat) :
    #(chain.toFinset ∩ powersetCard k univ) ≤ 1 := by
  -- TODO: discr-tree building is insanely slow here
  rw [card_le_one]
  grind [toFinset]

instance : Fintype (Chain n m) := inferInstanceAs (Fintype (Subtype _))
def c (n m : Nat) : Nat := Fintype.card (Chain n m)

def w (n m : Nat) : Rat := (1 - (m + 1) / (2 * n - m)) / c n m


theorem sum_w_eq_1 {n : Nat} (s : Finset (Fin (2 * n))) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 1 n, ∑ chain : Chain n m with s ∈ chain.toFinset, w n m = 1 := by
  simp_rw [sum_const, nsmul_eq_mul]
  unfold w c


theorem card_le_choose_of_isAntiChain (A : Finset (Finset (Fin (2 * n))))
    (hA : IsAntichain (· ⊆ ·) (SetLike.coe A)) : #A ≤ (2 * n).choose n := by
  rw [← ncard_maximalSet] -- Not suggested by infoview search???
  skip
  simp_rw [card_eq_sum_ones]





#check Finset.card_powersetCard
theorem foo' (A : Set (Finset (Fin (2 * n)))) (hA : IsAntichain (· ⊆ ·) A) :
  A.ncard ≤ (2 * n).choose n := by sorry

#check Nat.choose.eq_def -- Suggested by infoview search???
#check Nat.choose

/-
blacklist needs to exclude automatically generated theorems like Nat.choose.eq_def
but needs to include private theorems when in a module.
-/
def foo (n : Nat) : Nat :=
  if n + 3 = 3 then
    5
  else
    foo (n - 10)

open Lean
#eval Name.isInternalOrNum ``foo.eq_def
#eval Name.isBlackListed ``foo.eq_def

#eval Name.isBlackListed ``foo.eq_1
