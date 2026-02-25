/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Util
public meta import Mathlib.Control.Basic

import all Lean.Elab.Tactic.Induction

/-!
This file defines the tactic suggestions for `infoview_suggest` when the user clicks on
the name of a hypothesis.
-/

meta section

namespace InfoviewSearch

open Lean Meta Elab Tactic Server ProofWidgets Jsx

/-- Return some constants that may be suitable as eliminators for
the `induction` or `cases` tactic, using the given variable.

We consider all declarations that are marked `elab_as_elim`
and whose name starts with the name of the type in question.
For each of these, we also try removing a suffix `On`, `_on` or `'`.
-/
partial def getEliminatorCandidates (fvarId : FVarId) : MetaM (Array (Name × Option Bool)) := do
  let e ← fvarId.getType
  let .const type _ := (← whnf e).getAppFn | return #[]
  let mut eliminators : NameMap (Option Bool) := ∅
  -- Find the default `induction` eliminator
  let customEliminators ← getCustomEliminators
  if let some ind := customEliminators.map.find? (true, #[type]) then
    eliminators := eliminators.insert ind (some true)
  else
    if let some indVal ← isInductive? type then
      -- Only return `.rec` if the inductive type is recursive
      if indVal.isRec then
        -- check that `induction` is possible
        if indVal.all.length == 1 && !indVal.isNested then
          eliminators := eliminators.insert (mkRecName indVal.name) (some true)
  -- Find the default `cases` eliminator
  if let some ind := customEliminators.map.find? (false, #[type]) then
    eliminators := eliminators.insert ind (some false)
  else
    if let some indVal ← isInductive? type then
      -- Only return the `.casesOn` if the inductive type is not recursive
      if !indVal.isRec then
        eliminators := eliminators.insert (mkCasesOnName indVal.name) (some false)
  -- Find any other potential eliminators
  let types ← unfoldTypes e
  let env ← getEnv
  let { importedEntries, state } := Elab.Term.elabAsElim.ext.toEnvExtension.getState env
  eliminators := state.foldl (addEntry types env) eliminators
  eliminators := importedEntries.foldl (Array.foldl (addEntry types env)) eliminators
  return eliminators.toArray
where
  /-- Simetimes not all eliminators are tagged with `elab_as_elim`, so we try to find some other
  eliminators with similar names and check to see if they exist.-/
  addEntry (types : Std.HashSet Name) (env : Environment) (elims : NameMap (Option Bool))
      (elim : Name) : NameMap (Option Bool) := Id.run do
    -- TODO: these two recursion principles should really be deprecated.
    if elim matches `Nat.strongRecOn' | `Nat.strongRec' then return elims
    let .str pre str := elim | return elims
    unless types.contains pre do return elims
    let mut elims := elims
    if let some str' := str.dropSuffix? '\'' then
      let elim' := .str pre str'.toString
      if env.contains elim' then
        elims ← addEntry types env elims elim'
    if let some str' := str.dropSuffix? "_on" then
      let elim' := .str pre str'.toString
      if env.contains elim' then
        elims := elims.insertIfNew elim' none
    else if let some str' := str.dropSuffix? "On" then
      let elim' := .str pre str'.toString
      if env.contains elim' then
        elims := elims.insertIfNew elim' none
    else
      -- We typically don't want to suggest `inductionOn` or `induction_on`
      -- if `indunction` already existing.
      elims := elims.insertIfNew elim none
    return elims
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

/-- Determine whether the given eliminator is a valid eliminator, and whether to use it
with `induction` or `cases`. -/
def classifyEliminator (fvarId : FVarId) (eliminator : Name) (induction? : Option Bool) :
    InfoviewSearchM (Option ((Bool × Option Name) × ElimInfo × Array Expr)) := try? do
  let elimInfo ← getElimInfo eliminator
  let targets ← addImplicitTargets elimInfo #[.fvar fvarId]
  if let some induction := induction? then
    return ((induction, none), elimInfo, targets)
  forallTelescopeReducing elimInfo.elimType fun xs type ↦ do
    -- make sure that the eliminator is applies to the type we want.
    let .str typeName _ := eliminator | failure
    let .app _ arg := type | failure
    guard <| (← inferType arg).getAppFn.isConstOf typeName
    let motive := xs[elimInfo.motivePos]!
    for h : i in *...xs.size do
      if i != elimInfo.motivePos && !elimInfo.targetsPos.contains i then
        let x := xs[i]
        let xDecl ← x.fvarId!.getDecl
        if xDecl.binderInfo.isExplicit then
          let isRec ← forallTelescope xDecl.type fun ys _ ↦
            ys.anyM fun y ↦ return (← y.fvarId!.getType).getForallBody.getAppFn == motive
          if isRec then return ((true, eliminator), elimInfo, targets)
    return ((false, eliminator), elimInfo, targets)

open Widget Jsx in
/-- Create a suggestion for inserting `stx` and tactic name `tac`. -/
def mkInductionSuggestion (stx : TSyntax `tactic) (newGoals : Html)
    (induction : Bool) (using? : Option Name) :
    InfoviewSearchM Html := do
  -- Print the tactic without any argument (using a little syntax hack).
  let mut tac := if induction then "induction" else "cases"
  if using?.isSome then
    tac := tac ++ " using "
  let kind := if induction then ``Lean.Parser.Tactic.induction else ``Lean.Parser.Tactic.cases
  let mut title := <InteractiveCode fmt={← ppWithDoc tac kind}/>
  if let some eliminator := using? then
    let const ← addMessageContextPartial (.ofConstName eliminator)
    title := .element "span" #[] #[title, <InteractiveMessage msg={← WithRpcRef.mk const}/>]
  mkSuggestion stx <details style={json% { "width": "100%" }}>
    <summary style={json% { "cursor" : "pointer" }}> {title} </summary>
    {newGoals}
    </details>

def renderInduction (fvarId : FVarId) :
    InfoviewSearchM Html := do
  let candidates ← getEliminatorCandidates fvarId
  let n := mkIdent (← fvarId.getUserName)
  let candidates ← candidates.filterMapM fun (eliminator, induction?) ↦
    classifyEliminator fvarId eliminator induction?
  /- Sort the candidates in the order of `induction` before `cases`,
  and then by name length of the eliminator. -/
  let candidates := candidates.qsort fun (a, _) (b, _) ↦
    a.1 && !b.1 || a.1 == b.1 && (
      let a := a.2.getD .anonymous; let b := b.2.getD .anonymous
      (compare a.toString.length b.toString.length).then (b.cmp a) |>.isLT)
  let htmls ← candidates.filterMapM fun ((induction, using?), elimInfo, targets) ↦ do
    try
      some <$> withoutModifyingMCtx do
      let stx ← if induction
        then `(tactic| induction $n:ident $[using $(using?.map mkIdent):ident]?)
        else `(tactic| cases $n:ident $[using $(using?.map mkIdent):ident]?)
      let mctxOld ← getMCtx
      let go := if induction
        then evalInductionCore stx elimInfo targets
        else evalCasesCore stx elimInfo targets
      let newGoals ← (Tactic.run (← read).goal go).run'
      /- Some lemmas (e.g. `Int.inductionOn'` and `Int.strongRec`) add new metavariables
      to the goal, and for some reason the `induction` tactic doesn't throw an error about this.
      So we have to figure out ourselves when this happens. -/
      for newGoal in newGoals do
        let deps ← newGoal.getMVarDependencies
        if deps.any (mctxOld.findDecl? · |>.isNone) then
          throwError "Failure: elimination principle {elimInfo.elimExpr} creates metavariables, \
            so it is not suggested."
      let newGoals ← newGoals.mapM fun goal ↦ do
        let goal ← addMessageContextFull (.ofGoal goal)
        return <InteractiveMessage msg={← WithRpcRef.mk goal} />
      mkInductionSuggestion stx (.element "div" #[] newGoals.toArray) induction using?
    catch ex =>
      if infoview_search.debug.get (← getOptions) then
        return some <div><InteractiveMessage msg={← WithRpcRef.mk ex.toMessageData} /></div>
      else
        return none
  return .element "div" #[] htmls

public def suggestForHyp (hyp : FVarId) : InfoviewSearchM (Option Html) := do
  let mut htmls := #[]
  htmls := htmls.push (← renderInduction hyp)
  if htmls.isEmpty then
    return none
  return some <| .element "div" #[] htmls

/-
When clicking on a free variable,

If it is a term of a type, one typically wants to do induction/cases
If it is a proof, then additionally
- proof by contradiction
- specialization
- applying

-/

end InfoviewSearch
