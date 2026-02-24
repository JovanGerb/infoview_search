/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Util

/-!
This file defines the tactic suggestions for `infoview_suggest` when the user clicks on
the name of a hypothesis.
-/

public meta section

namespace InfoviewSearch

open Lean Meta Elab Tactic Server ProofWidgets Jsx

-- TODO: paste the whole induction tactic including all match arms.


/-- Return an array of constants that may be suitable as an eliminator for
the `induction` or `cases` tactic, over the given type.

The heuristic is very simple: we consider all declarations that are marked `elab_as_elim`
and whose name starts with the name of the type in question.
-/
partial def inductionCandidates (e : Expr) : MetaM (Array Name) := do
  let types ← unfoldTypes e
  let { importedEntries, state } := Elab.Term.elabAsElim.ext.toEnvExtension.getState (← getEnv)
  return Id.run do -- Probably good for efficiency in the big loop below.
  let mut result := #[]
  for eliminator in state do
    if types.any (·.isPrefixOf eliminator) then
      result := result.push eliminator
  for entry in importedEntries do
    for eliminator in entry do
      if types.any (·.isPrefixOf eliminator) then
        result := result.push eliminator
  return result
where
  unfoldTypes (e : Expr) : MetaM (Std.HashSet Name) := do
    let e ← whnfR e
    let s ←
      if let some e ← unfoldDefinition? e then
        unfoldTypes e
      else
        pure ∅
    if let .const t _ := e.getAppFn then
      return s.insert t
    else
      return s

/-- First try the cases tactic, and then the induction tactic,
and return a suggestion for the first one that works, if any. -/
def tryCasesInduction (var : Name) (eliminator : Option Name) : InfoviewSearchM (Option Html) := do
  let var := mkIdent var; let eliminator := eliminator.map mkIdent
  try
    withoutModifyingMCtx do
    let cases ← `(tactic| cases $var:ident $[using $eliminator]?)
    let (newGoals, _) ← runTactic (← read).goal cases
    let newGoals ← newGoals.mapM fun goal ↦
      return <InteractiveMessage msg={← WithRpcRef.mk (.ofGoal goal)} />
    mkTacticSuggestion cases cases (.element "div" #[] newGoals.toArray)
  catch _ => try
    withoutModifyingMCtx do
    let induction ← `(tactic| induction $var:ident $[using $eliminator]?)
    let (newGoals, _) ← runTactic (← read).goal induction
    let newGoals ← newGoals.mapM fun goal ↦
      return <InteractiveMessage msg={← WithRpcRef.mk (.ofGoal goal)} />
    mkTacticSuggestion induction induction (.element "div" #[] newGoals.toArray)
  catch _ =>
    return none

-- WIP
def renderInduction (fvarId : FVarId) : InfoviewSearchM (Option Html) := do
  -- let fvarName ← fvarId.getUserName
  -- let mut htmls := #[]
  -- if let some html ← tryCasesInduction fvarName none then
  --   htmls := htmls.push html
  -- for eliminator in ← inductionCandidates (← fvarId.getType) do
  --   if let some html ← tryCasesInduction fvarName eliminator then
  --     htmls := htmls.push html
  let some typeHead := (← whnf (← fvarId.getType)).getAppFn.constName? | return none
  unless ← isInductive typeHead do return none
  let name ← fvarId.getUserName
  let mut usingClause := none
  let elims ← getCustomEliminators
  if !elims.map.contains (true, #[typeHead]) then
    if (← getEnv).contains (typeHead.str "induction") then
      usingClause := some (mkIdent (typeHead.str "induction"))
  let tactic ← `(tactic| induction $(mkIdent name):ident $[using $usingClause]?)
  mkSuggestion (isText := true) ⟨tactic.1⟩ <| .text s!"induction on {name}"

def suggestForHyp (hyp : FVarId) : InfoviewSearchM (Option Html) := do
  let mut htmls := #[]
  if let some html ← renderInduction hyp then
    htmls := htmls.push html
  if htmls.isEmpty then
    return none
  return some <| .element "div" #[] htmls

end InfoviewSearch
