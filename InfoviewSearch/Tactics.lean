/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Util

import all Lean.Meta.PPGoal

public meta section

namespace InfoviewSearch

open Lean Meta ProofWidgets Jsx

def mkUnusedNameNumbered (names : NameSet) (name : Name) : Name :=
  if !names.contains name then name else
  let name' := name.appendAfter "₁"
  if !names.contains name' then name' else
  let name' := name.appendAfter "₂"
  if !names.contains name' then name' else
  let name' := name.appendAfter "₃"
  if !names.contains name' then name' else
  let name' := name.appendAfter "₄"
  if !names.contains name' then name' else
  let name' := name.appendAfter "₅"
  if !names.contains name' then name' else
  let name' := name.appendAfter "₆"
  if !names.contains name' then name' else
  let name' := name.appendAfter "₇"
  if !names.contains name' then name' else
  let name' := name.appendAfter "₈"
  if !names.contains name' then name' else
  name.appendAfter "₉"

/-- Pretty print the hypotheses and goal (which are created by the suggested `intro` call). -/
def renderIntro (intros : Array (Name × Expr)) (goal : Expr) : InfoviewSearchM Html := do
  let hyps ← intros.mapM fun (name, type) ↦ do
    return <div>
      <strong className="goal-hyp"> {.text name.toString} {.text " "} </strong>
      {.text ": "}
      <InteractiveCode fmt={← Widget.ppExprTagged type} />
      </div>
  let goal := <div key="goal">
    <strong className="goal-vdash">{.text "⊢ "}</strong>
    <InteractiveCode fmt={← Widget.ppExprTagged goal} />
    </div>
  return .element "div" #[("className", Json.str "font-code tl pre-wrap")] (hyps.push goal)

/-- Give a suggestion for the `intro` tactic.

TODO: suggest different depths of introducing, depending on unfolding
TODO: suggest `rintro rfl` when applicable.
-/
def suggestIntro : InfoviewSearchM (Option Html) := do
  unless (← read).pos == .root && (← read).hyp?.isNone do return none
  -- Only run `whnf` on the outer most type (via `getType'`).
  -- If the user wants to `intro` more, they can simply do it again.
  let goal ← (← read).goal.getType'
  unless goal.isForall do return none
  let usedNames : NameSet := (← getLCtx).decls.foldl (init := ∅) fun
    | s, some decl => s.insert decl.userName
    | s, _ => s
  forallTelescope (cleanupAnnotations := true) goal fun xs goal ↦ do
    let mut usedNames := usedNames
    let mut intros := #[]
    -- We make sure to not suggest `intro a` if `a` is the name of another free variable,
    -- instead falling back to `a₁`, `a₂` etc.
    -- We do not worry about overriding global constants names.
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let name ← if !decl.userName.hasMacroScopes then pure decl.userName
        else if ← isProp decl.type then pure `h
        else pure `x
      let name := mkUnusedNameNumbered usedNames name
      intros := intros.push (name, decl.type)
      usedNames := usedNames.insert name
    mkTacticSuggestion
      (← `(tactic| intro $[$(intros.map (mkIdent ·.1))]*))
      (← `(tactic| intro))
      (← renderIntro intros goal)

def renderRfl : InfoviewSearchM (Option Html) := do
  unless (← read).pos == .root && (← read).hyp?.isNone do return none
  try withoutModifyingMCtx (← read).goal.applyRfl catch _ => return none
  let tactic ← `(tactic| rfl)
  mkSuggestion (isText := true) tactic <| .text "reflexivity"

def renderTactic : InfoviewSearchM (Option Html) := do
  let mut tactics := #[]
  if let some html ← renderRfl then
    tactics := tactics.push html
  if let some html ← suggestIntro then
    tactics := tactics.push html
  if !tactics.isEmpty then
    return mkSuggestionList tactics <| .text "tactics"
  else
    return none

end InfoviewSearch
