/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Search.SectionState
public import Mathlib.Tactic.ApplyAt

public meta section

namespace InfoviewSearch
open Lean Meta Widget Server ProofWidgets Jsx

structure ApplyAtLemma where
  name : Premise

structure ApplyAtInfo where
  pasteInfo : PasteInfo
  target : Expr
  hyp : Name

structure ApplyAtKey where
  numGoals : Nat
  nameLenght : Nat
  replacementSize : Nat
  name : String
  newGoals : Array AbstractMVarsResult
deriving Inhabited

instance : Ord ApplyAtKey where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4)

def ApplyAtKey.isDuplicate (a b : ApplyAtKey) : MetaM Bool :=
  pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

/-- Return the `apply` tactic that performs the application. -/
private def tacticSyntax (lem : ApplyAtLemma) (i : ApplyAtInfo) : MetaM (TSyntax `tactic) := do
  -- let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab app.proof)
  `(tactic| apply $(mkIdent (← lem.name.unresolveName)) at $(mkIdent i.hyp))

set_option linter.style.emptyLine false in
/-- Generate a suggestion for applying `lem`. -/
def ApplyAtLemma.generateSuggestion (lem : ApplyAtLemma) (i : ApplyAtInfo) :
    MetaM (Result ApplyAtKey) :=
  withReducible do withNewMCtxDepth do
  let (_proof, mvars, binderInfos, replacement) ← lem.name.forallMetaTelescopeReducing
  let e ← inferType mvars.back!
  let mvars := mvars.pop
  unless ← isDefEq e i.target do throwError "{e} does not unify with {i.target}"
  synthAppInstances `infoview_search default mvars binderInfos false false
  let mut newGoals := #[]
  for mvar in mvars, bi in binderInfos do
    unless ← mvar.mvarId!.isAssigned do
      newGoals := newGoals.push (mvar.mvarId!, bi)

  let replacement ← instantiateMVars replacement
  let makesNewMVars ←
    pure (replacement.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome <||>
    newGoals.anyM fun goal ↦ do
      let type ← instantiateMVars <| ← goal.1.getType
      return (type.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome
  -- let proof ← instantiateMVars proof
  let key := {
    numGoals := newGoals.size
    nameLenght := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr (← g.1.getType)).pretty.length + s
    name := lem.name.toString
    newGoals := ← newGoals.mapM fun g => do abstractMVars (← g.1.getType)
  }
  let tactic ← tacticSyntax lem i
  let replacement ← ppExprTagged replacement
  let mut explicitGoals := #[]
  for (mvarId, bi) in newGoals do
    -- TODO: think more carefully about which goals should be displayed
    -- Are there lemmas where a hypothesis is marked as implicit,
    -- which we would still want to show as a new goal?
    if bi.isExplicit then
      explicitGoals := explicitGoals.push (← ppExprTagged (← mvarId.getType))
  let mut htmls := #[<InteractiveCode fmt={replacement}/>]
  for newGoal in explicitGoals do
    htmls := htmls.push
      <div> <strong className="goal-vdash">⊢ </strong> <InteractiveCode fmt={newGoal}/> </div>
  let filtered ←
    if !makesNewMVars then
      some <$> mkSuggestion tactic i.pasteInfo (.element "div" #[] htmls)
    else
      pure none
  htmls := htmls.push (<div> {← lem.name.toHtml} </div>)
  let unfiltered ← mkSuggestion tactic i.pasteInfo (.element "div" #[] htmls)
  let pattern ← forallTelescopeReducing (← lem.name.getType) fun xs _ => do
    ppExprTagged (← inferType xs.back!)
  return { filtered, unfiltered, key, pattern }

end InfoviewSearch
