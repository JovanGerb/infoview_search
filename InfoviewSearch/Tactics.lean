/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Util

public meta section

namespace InfoviewSearch

open Lean Meta ProofWidgets

def mkUnusedNameNumbered (lctx : LocalContext) (name : Name) : Name :=
  if !lctx.usesUserName name then name else
  let name' := name.appendAfter "₁"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₂"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₃"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₄"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₅"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₆"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₇"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₈"
  if !lctx.usesUserName name' then name' else
  name.appendAfter "₉"

def renderIntro (loc : SubExpr.GoalsLocation) : InfoviewSearchM (Option Html) := do
  let .target pos := loc.loc | return none
  unless pos == .root do return none
  -- Only run `whnf` on the outer most type.
  -- If the user wants more `intro`, they can do that separately again.
  let goal ← loc.mvarId.getType'
  unless goal.isForall do return none
  forallTelescope goal fun xs _ ↦ do
    let text := match ← isProof xs[0]!, xs.size == 1 with
      | true, true => "introduce the hypothesis"
      | true, false => "introduce the hypotheses"
      | false, true => "introduce the variable"
      | false, false => "introduce the variables"
    let mut lctx ← getLCtx
    let mut names := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let name ← if ← isProp decl.type then pure `h else
        if decl.userName.hasMacroScopes then pure decl.userName.eraseMacroScopes
        else pure `x
      let name := mkUnusedNameNumbered lctx name
      names := names.push name
      lctx := lctx.setUserName x.fvarId! name
    let tactic ← `(tactic| intro $[$(names.map mkIdent)]*)
    mkSuggestion (isText := true) tactic <| .text text

def renderRfl (loc : SubExpr.GoalsLocation) : InfoviewSearchM (Option Html) := do
  let .target pos := loc.loc | return none
  unless pos == .root do return none
  try withoutModifyingMCtx loc.mvarId.applyRfl catch _ => return none
  let tactic ← `(tactic| rfl)
  mkSuggestion (isText := true) tactic <| .text "reflexivity"

def renderInduction (loc : SubExpr.GoalLocation) : InfoviewSearchM (Option Html) := do
  let .hyp fvarId := loc | return none
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

def renderTactic (loc : SubExpr.GoalsLocation) : InfoviewSearchM (Option Html) := do
  let mut tactics := #[]
  if let some html ← renderRfl loc then
    tactics := tactics.push html
  if let some html ← renderInduction loc.loc then
    tactics := tactics.push html
  if let some html ← renderIntro loc then
    tactics := tactics.push html
  if !tactics.isEmpty then
    return mkListElement tactics <| .text "tactics"
  else
    return none

end InfoviewSearch
