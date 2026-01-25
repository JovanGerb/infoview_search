/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
-/
module

public import InfoviewSearch.Util

public meta section

namespace InfoviewSearch.Grw

/-! ### Caching -/

open Lean Meta Mathlib.Tactic

/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
structure GRewriteLemma where
  /-- The lemma -/
  name : Premise
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
  /-- `relName` is the relation of the lemma. -/
  relName : Name

structure GRewritePos where
  relation : Expr
  relName : Name
  symm : Bool

-- TODO: when the relation is symmetric, then look up both directions in the discr tree.

/-! ### Checking rewrite lemmas -/

def fakeDischarger (ref : IO.Ref (Option Expr)) (goal : MVarId) : MetaM Bool := do
  ref.set (← instantiateMVars (← goal.getType))
  Meta.throwIsDefEqStuck

def getGRewritePos? (rootExpr : Expr) (subExpr : SubExpr) (hyp? : Bool) :
    MetaM (Option GRewritePos) := do
  withLocalDeclD `_a (← inferType subExpr.expr) fun fvar => do
  let root' ← replaceSubexpr (fun _ => pure (GCongr.mkHoleAnnotation fvar)) subExpr.pos rootExpr
  let imp := Expr.forallE `_a rootExpr root' .default
  let gcongrGoal ← mkFreshExprMVar imp
  let ref ← IO.mkRef none
  try
    catchInternalId isDefEqStuckExceptionId
      (discard <| gcongrGoal.mvarId!.gcongr false [] (mainGoalDischarger := fakeDischarger ref))
      fun _ => pure ()
  catch _ =>
    return none
  let some e@(.app (.app relation lhs) rhs) ← ref.get | return none
  let .const relName _ := relation.getAppFn | return none
  if relName matches ``Eq | ``Iff then return none
  let symm ←
    if lhs.cleanupAnnotations == fvar then pure hyp?
    else if rhs.cleanupAnnotations == fvar then pure !hyp?
    else throwError "{e} doesn't have {fvar} on either side"
  return some { relation, relName, symm }

structure RewriteInfo where
  numGoals : Nat
  nameLenght : Nat
  replacementSize : Nat
  name : String
  -- TODO: in this implementation, we conclude that two rewrites are the same if they
  -- rewrite into the same expression. But there can be two rewrites that have
  -- different side conditions!
  replacement : AbstractMVarsResult
deriving Inhabited

/-- A rewrite lemma that has been applied to an expression. -/
structure GRewrite extends GRewriteLemma where
  /-- The proof of the rewrite -/
  proof : Expr
  /-- The replacement expression obtained from the rewrite -/
  replacement : Expr
  /-- The extra goals created by the rewrite -/
  extraGoals : Array (MVarId × BinderInfo)
  /-- Whether the rewrite introduces a new metavariable in the replacement expression -/
  makesNewMVars : Bool
  /-- Whether the rewrite is reflexive -/
  isRefl : Bool
  info : RewriteInfo
  justLemmaName : Bool
  hyp? : Option Name
  occ : Option Nat

set_option linter.style.emptyLine false in
/-- If `thm` can be used to rewrite `e`, return the rewrite. -/
def checkGRewrite (lem : GRewriteLemma) (rootExpr : Expr) (subExpr : SubExpr) (gpos : GRewritePos)
    (hyp? : Option Name) (occ : Option Nat) : MetaM (Option GRewrite) := withReducible do
  let e := subExpr.expr
  unless lem.relName == gpos.relName && lem.symm == gpos.symm do
    return none
  let thm ← match lem.name with
    | .const name => mkConstWithFreshMVarLevels name
    | .fvar fvarId => pure (.fvar fvarId)
  withTraceNodeBefore `infoview_search (return m!
    "grewriting {e} by {if lem.symm then "← " else ""}{thm}") do
  let (mvars, binderInfos, eqn) ← forallMetaTelescopeReducing (← inferType thm)
  let .app (.app rel lhs) rhs := (← instantiateMVars eqn).cleanupAnnotations | return none
  unless ← isDefEq rel gpos.relation do
    return none
  let (lhs, rhs) := if lem.symm then (rhs, lhs) else (lhs, rhs)
  let lhsOrig := lhs; let mctxOrig ← getMCtx
  let unifies ← withTraceNodeBefore `infoview_search (return m! "unifying {e} =?= {lhs}")
    (isDefEq e lhs)
  unless unifies do return none
  -- just like in `kabstract`, we compare the `HeadIndex` and number of arguments
  let lhs ← instantiateMVars lhs
  -- TODO: if the `headIndex` doesn't match, then use `gsimp` instead of `rw` in the suggestion???
  if lhs.toHeadIndex != e.toHeadIndex || lhs.headNumArgs != e.headNumArgs then
    return none
  try synthAppInstances `infoview_search default mvars binderInfos false false
  catch _ => return none
  let mut extraGoals := #[]
  for mvar in mvars, bi in binderInfos do
    unless ← mvar.mvarId!.isAssigned do
      extraGoals := extraGoals.push (mvar.mvarId!, bi)

  let replacement ← instantiateMVars rhs
  let makesNewMVars ←
    pure (replacement.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome <||>
    extraGoals.anyM fun goal ↦ do
      let type ← instantiateMVars <| ← goal.1.getType
      return (type.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome
  let proof ← instantiateMVars (mkAppN thm mvars)
  let isRefl ← isExplicitEq e replacement
  let justLemmaName ← withMCtx mctxOrig do kabstractFindsPositions rootExpr lhsOrig subExpr.pos
  let info := {
    numGoals := extraGoals.size
    nameLenght := lem.name.length
    replacementSize := (← ppExpr replacement).pretty.length
    name := lem.name.toString
    replacement := ← abstractMVars replacement
  }
  return some { lem with
    proof, replacement, extraGoals, makesNewMVars, isRefl, info, justLemmaName, hyp?, occ }

def RewriteInfo.lt (a b : RewriteInfo) : Bool :=
  Ordering.isLT <|
  (compare a.1 b.1).then <|
  (compare a.2 b.2).then <|
  (compare a.3 b.3).then <|
  (compare a.4 b.4)

def RewriteInfo.isDuplicate (a b : RewriteInfo) : MetaM Bool :=
  pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

open Widget ProofWidgets Jsx Server

/-- Return the rewrite tactic that performs the rewrite. -/
def tacticSyntax (grw : GRewrite) : MetaM (TSyntax `tactic) := do
  let proof ← if grw.justLemmaName then
      `(term| $(mkIdent <| ← grw.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab grw.proof)
  mkRewrite grw.occ grw.symm proof grw.hyp? (g := true)

/-- `RwResult` stores the information from a rewrite lemma that was successful. -/
structure RwResult where
  /-- `filtered` will be shown in the filtered view. -/
  filtered : Option Html
  /-- `unfiltered` will be shown in the unfiltered view. -/
  unfiltered : Html
  /-- `info` is used for sorting and comparing rewrite theorems. -/
  info : RewriteInfo
  /-- The `pattern` of the first lemma in a section is shown in the header of that section. -/
  pattern : CodeWithInfos
deriving Inhabited

instance : LT RwResult where
  lt a b := a.info.lt b.info

instance : DecidableLT RwResult := fun a b => by
  dsimp [LT.lt]; infer_instance

/-- Construct the `Result` from a `GRewrite`. -/
def GRewrite.toResult (grw : GRewrite) (pasteInfo : PasteInfo) : MetaM RwResult := do
  let tactic ← tacticSyntax grw
  let replacement ← ppExprTagged grw.replacement
  let mut extraGoals := #[]
  for (mvarId, bi) in grw.extraGoals do
    -- TODO: think more carefully about which goals should be displayed
    -- Are there lemmas where a hypothesis is marked as implicit,
    -- which we would still want to show as a new goal?
    if bi.isExplicit then
      extraGoals := extraGoals.push (← ppExprTagged (← mvarId.getType))
  let prettyLemma ← ppPremiseTagged grw.name
  let html (showNames : Bool) :=
    mkSuggestionElement tactic pasteInfo <|
    let extraGoals := extraGoals.flatMap fun extraGoal =>
      #[<div> <strong className="goal-vdash">⊢ </strong> <InteractiveCode fmt={extraGoal}/> </div>];
    .element "div" #[] <|
      #[<InteractiveCode fmt={replacement}/>] ++ extraGoals ++
        if showNames then #[<div> <InteractiveCode fmt={prettyLemma}/> </div>] else #[]
  let lemmaType ← match grw.name with
    | .const name => (·.type) <$> getConstInfo name
    | .fvar fvarId => inferType (.fvar fvarId)
  return {
    filtered := ← if !grw.isRefl && !grw.makesNewMVars then (some <$> html false) else pure none
    unfiltered := ← html true
    info := grw.info
    pattern := ← pattern lemmaType
  }
where
  /-- Render the matching side of the rewrite lemma.
  This is shown at the header of each section of rewrite results. -/
  pattern (type : Expr) : MetaM CodeWithInfos := withReducible do
    forallTelescopeReducing type fun _ e => do
      let .app (.app _ lhs) rhs := (← instantiateMVars e).cleanupAnnotations
        | throwError "Expected relation, not {indentExpr e}"
      ppExprTagged <| if grw.symm then rhs else lhs

/-- `generateSuggestion` is called in parallel for all rewrite lemmas.
- If the lemma succeeds, return a `RwResult`.
- If the lemma fails, return `none`
- If the attempt throws an error, return the error as `Html`.

Note: we use two `try`-`catch` clauses, because we rely on `ppConstTagged`
in the first `catch` branch, which could (in principle) throw an error again.
-/
def generateSuggestion (rootExpr : Expr) (subExpr : SubExpr) (pasteInfo : PasteInfo)
    (gpos : GRewritePos) (hyp? : Option Name) (occ : Option Nat) (lem : GRewriteLemma) :
    MetaM <| Task (Except Html <| Option RwResult) := do
  BaseIO.asTask <| EIO.catchExceptions (← dropM do withCurrHeartbeats do
    have : MonadExceptOf _ MetaM := MonadAlwaysExcept.except
    try .ok <$> withNewMCtxDepth do
      Core.checkSystem "infoview_search"
      let some rewrite ← checkGRewrite lem rootExpr subExpr gpos hyp? occ | return none
      some <$> rewrite.toResult pasteInfo
    catch e => withCurrHeartbeats do
      return .error
        <li>
          An error occurred when processing generalized rewrite lemma
          <InteractiveCode fmt={← ppPremiseTagged lem.name}/>:
          <br/>
          <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData} />
        </li>)
    fun e =>
      return .error
        <li>
          An error occurred when pretty printing generalized rewrite lemma {.text lem.1.toString}:
          <br/>
          <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData} />
        </li>

/-! ### Maintaining the state of the widget -/

/-- `SectionState` is the part of `WidgetState` corresponding to each section of suggestions. -/
structure SectionState where
  /-- Whether the rewrites are using a local hypothesis, a local theorem, or an imported theorem. -/
  kind : PremiseKind
  /-- The results of the theorems that successfully rewrite. -/
  results : Array RwResult
  /-- The computations for rewrite theorems that have not finished evaluating. -/
  pending : Array (Task (Except Html <| Option RwResult))

def SectionState.update (s : SectionState) : MetaM (Array Html × SectionState) := do
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
  findDuplicate (result : RwResult) (results : Array RwResult) : MetaM (Option Nat) := do
    unless result.filtered.isSome do
      return none
    results.findIdxM? fun res =>
      pure res.filtered.isSome <&&> res.info.isDuplicate result.info

/-- Render one section of rewrite results. -/
def SectionState.render (filter : Bool) (s : SectionState) : Option Html := do
  let head ← s.results[0]?
  let suffix := match s.kind with
    | .hypothesis => " (local hypotheses)"
    | .fromFile => " (lemmas from current file)"
    | .fromImport => ""
  let suffix := if s.pending.isEmpty then suffix else suffix ++ " ⏳"
  let htmls := if filter then s.results.filterMap (·.filtered) else s.results.map (·.unfiltered)
  guard (!htmls.isEmpty)
  return mkListElement htmls
    <span> grw: <InteractiveCode fmt={head.pattern}/> {.text suffix} </span>

end InfoviewSearch.Grw
