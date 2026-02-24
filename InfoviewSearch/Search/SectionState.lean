/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
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
  /-- `key` is used for sorting and comparing theorems. -/
  key : α
  /-- The `pattern` of the first lemma in a section is shown in the header of that section. -/
  pattern : CodeWithInfos
deriving Inhabited

instance [Ord α] : Ord (Result α) := ⟨(compare ·.key ·.key)⟩
instance [Ord α] : LT (Result α) := ltOfOrd

/-! ### Maintaining the state of the widget -/

/-- The source of a library lemma -/
inductive Source where
  /-- A local hypothesis -/
  | hypothesis
  /-- A lemma from the current file -/
  | fromFile
  /-- A lemma from an imported file -/
  | fromImport

/-- `SectionState` is the part of `WidgetState` corresponding to each section of suggestions. -/
structure SectionState (α : Type) where
  /-- Whether the rewrites are using a local hypothesis, a local theorem, or an imported theorem. -/
  source : Source
  /-- The results of the theorems that successfully applied. -/
  results : Array (Result α)
  /-- The results of the theorems that threw an error when trying to apply them. -/
  errors : Array Html
  /-- The computations for theorems that have not finished evaluating. -/
  pending : Array (Task (Except Html (Option (Result α))))


def SectionState.new (source : Source) (tasks : Array (Task (Except Html (Option (Result α))))) :
    SectionState α where
  source; results := #[]; errors := #[]; pending := tasks
/-- Insert the new result `res` into the array `arr` of already existing results.

We maintain the invariants that `results` is sorted, and for each set of duplicate results,
only the first one can have the `filtered` field set to `some`. -/
@[specialize]
def Result.insertInArray (res : Result α) (arr : Array (Result α)) (isDup : α → α → MetaM Bool) :
    MetaM (Array (Result α)) := do
  if let some idx ← findDuplicate res arr then
    if res < arr[idx]! then
      return (arr.modify idx ({ · with filtered := none })).binInsert (· < ·) res
    else
      return arr.binInsert (· < ·) { res with filtered := none }
  else
    return arr.binInsert (· < ·) res
where
  /-- Check if there is already a duplicate of `result` in `results`,
  for which both appear in the filtered view. -/
  findDuplicate (result : Result α) (results : Array (Result α)) : MetaM (Option Nat) := do
    unless result.filtered.isSome do
      return none
    results.findIdxM? fun res =>
      pure res.filtered.isSome <&&> isDup res.key result.key

/-- Go through the pending entries in the section state, and each of the entries that have
finished evaluating will be added to the finished result. -/
@[specialize]
def SectionState.update (s : SectionState α) (isDup : α → α → MetaM Bool) :
    MetaM (SectionState α) := do
  let mut pending := #[]
  let mut results := s.results
  let mut errors := s.errors
  for t in s.pending do
    if !(← IO.hasFinished t) then
      pending := pending.push t
    else
      match t.get with
      | .ok (some res) => results ← res.insertInArray results isDup
      | .ok none => pure ()
      | .error e => errors := errors.push e
  return ({ source := s.source, results, errors, pending })

/-- Render one section of the library search results. -/
def SectionState.render (filter : Bool) (s : SectionState α) (tactic : String) : Option Html :=
  if s.results.isEmpty && s.errors.isEmpty then none else some <|
  let head :=
    if let some head := s.results[0]? then <InteractiveCode fmt={head.pattern}/> else .text ""
  let suffix := match s.source with
    | .hypothesis => " (local hypotheses)"
    | .fromFile => " (lemmas from current file)"
    | .fromImport => ""
  let suffix := if s.pending.isEmpty then suffix else suffix ++ " ⏳"
  let htmls := if filter then s.results.filterMap (·.filtered) else s.results.map (·.unfiltered)
  let htmls := if s.errors.isEmpty then htmls else htmls.push <| renderErrors s.errors
  mkSuggestionList htmls <span> {.text s!"{tactic}: "}{head} {.text suffix} </span>
where
  /-- Render the error messages -/
  renderErrors (errors : Array Html) : Html :=
    <details «open»={true}>
      <summary className="mv2 pointer">
        <span «class»="error"> Failures: </span>
      </summary>
      {Html.element "ul" #[("style", json% { "padding-left" : "30px"})] errors}
    </details>

end InfoviewSearch
