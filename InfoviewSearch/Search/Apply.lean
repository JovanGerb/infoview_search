/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Search.SectionState

public meta section

namespace InfoviewSearch
open Lean Meta ProofWidgets Jsx

structure ApplyLemma where
  name : Premise

structure ApplyInfo where
  target : Expr

structure ApplyKey where
  numGoals : Nat
  nameLenght : Nat
  replacementSize : Nat
  name : String
  newGoals : Array AbstractMVarsResult
deriving Inhabited

instance : Ord ApplyKey where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4)

def ApplyKey.isDuplicate (a b : ApplyKey) : MetaM Bool :=
  pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

/-- Return the `apply` tactic that performs the application. -/
private def tacticSyntax (proof : Expr) (useExact : Bool) : MetaM (TSyntax `tactic) := do
  let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
  if useExact then
    `(tactic| exact $proof)
  else
    `(tactic| refine $proof)

set_option linter.style.emptyLine false in
/-- Generate a suggestion for applying `lem`. -/
def ApplyLemma.generateSuggestion (i : ApplyInfo) (lem : ApplyLemma) :
    InfoviewSearchM (Result ApplyKey) :=
  withReducible do withNewMCtxDepth do
  let (proof, mvars, binderInfos, e) ← lem.name.forallMetaTelescopeReducing
  unless ← isDefEq e i.target do throwError "{e} does not unify with {i.target}"
  synthAppInstances `infoview_search default mvars binderInfos false false
  let mut newGoals := #[]
  for mvar in mvars, bi in binderInfos do
    unless ← mvar.mvarId!.isAssigned do
      newGoals := newGoals.push (← instantiateMVars (← inferType mvar), bi)

  let makesNewMVars := newGoals.any fun goal =>
    (goal.1.findMVar? (mvars.contains <| .mvar ·)).isSome
  let proof ← instantiateMVars proof
  let key := {
    numGoals := newGoals.size
    nameLenght := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr g.1).pretty.length + s
    name := lem.name.toString
    newGoals := ← newGoals.mapM (abstractMVars ·.1)
  }
  let tactic ← tacticSyntax proof newGoals.isEmpty
  let mut explicitGoals := #[]
  for (mvarId, bi) in newGoals do
    -- TODO: think more carefully about which goals should be displayed
    -- Are there lemmas where a hypothesis is marked as implicit,
    -- which we would still want to show as a new goal?
    if bi.isExplicit then
      explicitGoals := explicitGoals.push
        <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml mvarId} </div>
  let htmls := if explicitGoals.isEmpty then #[.text "Goal accomplished! 🎉"] else explicitGoals
  let filtered ←
    if !makesNewMVars then
      some <$> mkSuggestion tactic (.element "div" #[] htmls) newGoals.isEmpty
    else
      pure none
  let htmls := htmls.push (<div> {← lem.name.toHtml} </div>)
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls) newGoals.isEmpty
  let pattern ← forallTelescope (← lem.name.getType) fun _ e => exprToHtml e
  return { filtered, unfiltered, key, pattern }

end InfoviewSearch
