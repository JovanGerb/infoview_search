module

public import InfoviewSearch.Util

public meta section

namespace InfoviewSearch
open Lean Widget ProofWidgets Jsx

variable {α : Type} [Ord α] [Inhabited α]

/-- `Result` stores the information from a rewrite lemma that was successful. -/
structure Result (α : Type) where
  /-- `filtered` will be shown in the filtered view. -/
  filtered : Option Html
  /-- `unfiltered` will be shown in the unfiltered view. -/
  unfiltered : Html
  /-- `info` is used for sorting and comparing theorems. -/
  info : α
  /-- The `pattern` of the first lemma in a section is shown in the header of that section. -/
  pattern : CodeWithInfos
deriving Inhabited

instance [Ord α] : Ord (Result α) := ⟨(compare ·.info ·.info)⟩
instance [Ord α] : LT (Result α) := ltOfOrd

/-! ### Maintaining the state of the widget -/

/-- `SectionState` is the part of `WidgetState` corresponding to each section of suggestions. -/
structure SectionState (α : Type) where
  /-- Whether the rewrites are using a local hypothesis, a local theorem, or an imported theorem. -/
  kind : PremiseKind
  /-- The results of the theorems that successfully rewrite. -/
  results : Array (Result α)
  /-- The computations for rewrite theorems that have not finished evaluating. -/
  pending : Array (Task (Except Html (Option (Result α))))

/-- Go through the pending entries in the section state, and each of the entries that have
finished evaluating will be added to the finished result.

We maintain the invariants that `results` is sorted, and for each set of duplicate results,
only the first one can have the `filtered` field set to `some`.
-/
def SectionState.update (s : SectionState α) (isDup : α → α → MetaM Bool) :
    MetaM (Array Html × SectionState α) := do
  let mut pending := #[]
  let mut results := s.results
  let mut exceptions := #[]
  for t in s.pending do
    if !(← IO.hasFinished t) then
      pending := pending.push t
    else
      match t.get with
      | .error e => exceptions := exceptions.push e
      | .ok none => pure ()
      | .ok (some result) =>
        if let some idx ← findDuplicate result results then
          if result < results[idx]! then
            results := results.modify idx ({ · with filtered := none })
            results := results.binInsert (· < ·) result
          else
            results := results.binInsert (· < ·) { result with filtered := none }
        else
          results := results.binInsert (· < ·) result
  return (exceptions, { s with pending, results })
where
  /-- Check if there is already a duplicate of `result` in `results`,
  for which both appear in the filtered view. -/
  findDuplicate (result : Result α) (results : Array (Result α)) : MetaM (Option Nat) := do
    unless result.filtered.isSome do
      return none
    results.findIdxM? fun res =>
      pure res.filtered.isSome <&&> isDup res.info result.info

/-- Render one section of rewrite results. -/
def SectionState.render (filter : Bool) (s : SectionState α) (tactic : String) : Option Html := do
  let head ← s.results[0]?
  let suffix := match s.kind with
    | .hypothesis => " (local hypotheses)"
    | .fromFile => " (lemmas from current file)"
    | .fromImport => ""
  let suffix := if s.pending.isEmpty then suffix else suffix ++ " ⏳"
  guard (!s.results.isEmpty)
  let htmls := if filter then s.results.filterMap (·.filtered) else s.results.map (·.unfiltered)
  return mkListElement htmls
    <span> {.text s!"{tactic}: "}<InteractiveCode fmt={head.pattern}/> {.text suffix} </span>

end InfoviewSearch
