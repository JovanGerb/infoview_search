/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
-/
module

public import Mathlib.Lean.Meta.RefinedDiscrTree
public import InfoviewSearch.RefreshComponent

public meta section

namespace InfoviewSearch.Grw

/-! ### Caching -/

open Lean Meta RefinedDiscrTree Mathlib.Tactic

/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
structure GRewriteLemma where
  /-- The lemma -/
  name : Premise
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
  /-- `relName` is the relation of the lemma. -/
  relName : Name

/-- Try adding the lemma to the `RefinedDiscrTree`. -/
def addGRewriteEntry (name : Name) (cinfo : ConstantInfo) :
    MetaM (List (GRewriteLemma × List (Key × LazyEntry))) := do
  -- we start with a fast-failing check to see if the lemma has the right shape
  let .app (.app f _) _ := cinfo.type.getForallBody | return []
  let .const relName _ := f.getAppFn | do return []
  if relName matches ``Eq | ``Iff then return []
  setMCtx {} -- recall that the metavariable context is not guaranteed to be empty at the start
  let (_, _, e) ← forallMetaTelescope cinfo.type
  let .app (.app _ lhs) rhs := e | return []
  let mut result := []
  unless isBadMatch lhs do
    result :=
      ({ name := .const name, symm := false, relName }, ← initializeLazyEntryWithEta lhs) :: result
  unless isBadMatch rhs do
    result :=
      ({ name := .const name, symm := true, relName }, ← initializeLazyEntryWithEta rhs) :: result
  return result

/-- Try adding the local hypothesis to the `RefinedDiscrTree`. -/
def addLocalGRewriteEntry (decl : LocalDecl) :
    MetaM (List (GRewriteLemma × List (Key × LazyEntry))) :=
  withReducible do
  let (_, _, e) ← forallMetaTelescope decl.type
  let .app (.app f lhs) rhs ← instantiateMVars e | return []
  let .const relName _ := f.getAppFn | return []
  if relName matches ``Eq | ``Iff then return []
  return [
    ({ name := .fvar decl.fvarId, symm := false, relName }, ← initializeLazyEntryWithEta lhs),
    ({ name := .fvar decl.fvarId, symm := true, relName }, ← initializeLazyEntryWithEta rhs)]

initialize importedRewriteLemmasExt :
    EnvExtension (IO.Ref (Option (RefinedDiscrTree GRewriteLemma))) ←
  registerEnvExtension (IO.mkRef none)

structure GRewritePos where
  relation : Expr
  relName : Name
  symm : Bool

-- TODO: when the relation is symmetric, then look up both directions in the discr tree.

/-- Get all potential rewrite lemmas from the imported environment.
By setting the `librarySearch.excludedModules` option, all lemmas from certain modules
can be excluded. -/
def getImportCandidates (e : Expr) (gpos : Option Grw.GRewritePos) :
    MetaM (MatchResult GRewriteLemma) := do
  unless gpos.isSome do
    return {}
  findImportMatches importedRewriteLemmasExt addGRewriteEntry
    /-
    5000 constants seems to be approximately the right number of tasks
    Too many means the tasks are too long.
    Too few means less cache can be reused and more time is spent on combining different results.

    With 5000 constants per task, we set the `HashMap` capacity to 256,
    which is the largest capacity it gets to reach.
    -/
    (constantsPerTask := 5000) (capacityPerTask := 256) e

/-- Get all potential rewrite lemmas from the current file. Exclude lemmas from modules
in the `librarySearch.excludedModules` option. -/
def getModuleCandidates (e : Expr) (parentDecl? : Option Name) :
    MetaM (MatchResult GRewriteLemma) := do
  let moduleTreeRef ← createModuleTreeRef fun name cinfo ↦
    if name == parentDecl? then return [] else addGRewriteEntry name cinfo
  findModuleMatches moduleTreeRef e

/-- Construct the `RefinedDiscrTree` of all local hypotheses. -/
def getHypotheses (except : Option FVarId) : MetaM (RefinedDiscrTree GRewriteLemma) := do
  let mut tree : PreDiscrTree GRewriteLemma := {}
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && except.all (· != decl.fvarId) then
      for (val, entries) in ← addLocalGRewriteEntry decl do
        for (key, entry) in entries do
          tree := tree.push key (entry, val)
  return tree.toRefinedDiscrTree

/-- Return all applicable hypothesis rewrites of `e`. Similar to `getImportCandidates`. -/
def getHypothesisCandidates (e : Expr) (except : Option FVarId) (gpos : Option Grw.GRewritePos) :
    MetaM (MatchResult GRewriteLemma) := do
  unless gpos.isSome do
    return {}
  let (candidates, _) ← (← getHypotheses except).getMatch e (unify := false) (matchRootStar := true)
  MonadExcept.ofExcept candidates



/-! ### Checking rewrite lemmas -/

def fakeDischarger (ref : IO.Ref (Option Expr)) (goal : MVarId) : MetaM Bool := do
  ref.set (← instantiateMVars (← goal.getType))
  Meta.throwIsDefEqStuck

def getGRewritePos? (e : Expr) (pos : ExprWithPos) (hyp? : Bool) : MetaM (Option GRewritePos) := do
  withLocalDeclD `_a (← inferType e) fun fvar => do
  let root' ← replaceSubexpr (fun _ => pure (GCongr.mkHoleAnnotation fvar)) pos.targetPos pos.root
  let imp := Expr.forallE `_a pos.root root' .default
  let gcongrGoal ← mkFreshExprMVar imp
  let ref ← IO.mkRef none
  try
    catchInternalId isDefEqStuckExceptionId
      (discard <| gcongrGoal.mvarId!.gcongr false [] (mainGoalDischarger := fakeDischarger ref))
      fun _ => pure ()
  catch _ =>
    return none
  let some (.app (.app relation lhs) rhs) ← ref.get | return none
  let .const relName _ := relation.getAppFn | return none
  if relName matches ``Eq | ``Iff then return none
  let symm ←
    if lhs.cleanupAnnotations == fvar then pure hyp?
    else if rhs.cleanupAnnotations == fvar then pure !hyp?
    else throwError "{(← ref.get).get!} doesn't have {fvar} on either side"
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
structure Rewrite extends GRewriteLemma where
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

set_option linter.style.emptyLine false in
/-- If `thm` can be used to rewrite `e`, return the rewrite.
HACK: the `name` argument is set to `FVarId.name` in the local rewrite case.
This works conveniently. -/
def checkGRewrite (lem : GRewriteLemma) (e : Expr) (gpos : GRewritePos) (pos : ExprWithPos) :
    MetaM (Option Rewrite) := withReducible do
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
  -- TODO: if the `headIndex` doesn't match, then use `simp_rw` instead of `rw` in the suggestion,
  -- instead of just not showing the suggestion.
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
  let justLemmaName ← withMCtx mctxOrig do kabstractFindsPositions lhsOrig pos
  let info := {
    numGoals := extraGoals.size
    nameLenght := lem.name.length
    replacementSize := (← ppExpr replacement).pretty.length
    name := lem.name.toString
    replacement := ← abstractMVars replacement
  }
  return some
    { lem with proof, replacement, extraGoals, makesNewMVars, isRefl, info, justLemmaName }

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
def tacticSyntax (rw : Rewrite) (pasteInfo : RwPasteInfo) :
    MetaM (TSyntax `tactic) := do
  let proof ← if rw.justLemmaName then
      `(term| $(mkIdent <| ← rw.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab rw.proof)
  mkRewrite pasteInfo.occ rw.symm proof pasteInfo.hyp? (g := true)

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

/-- Construct the `Result` from a `Rewrite`. -/
def Rewrite.toResult (rw : Rewrite) (pasteInfo : RwPasteInfo) : MetaM RwResult := do
  let tactic ← tacticSyntax rw pasteInfo
  let replacement ← ppExprTagged rw.replacement
  let mut extraGoals := #[]
  for (mvarId, bi) in rw.extraGoals do
    -- TODO: think more carefully about which goals should be displayed
    -- Are there lemmas where a hypothesis is marked as implicit,
    -- which we would still want to show as a new goal?
    if bi.isExplicit then
      extraGoals := extraGoals.push (← ppExprTagged (← mvarId.getType))
  let prettyLemma ← ppPremiseTagged rw.name
  let html (showNames : Bool) :=
    mkSuggestionElement tactic pasteInfo.toPasteInfo <|
    let extraGoals := extraGoals.flatMap fun extraGoal =>
      #[<div> <strong className="goal-vdash">⊢ </strong> <InteractiveCode fmt={extraGoal}/> </div>];
    .element "div" #[] <|
      #[<InteractiveCode fmt={replacement}/>] ++ extraGoals ++
        if showNames then #[<div> <InteractiveCode fmt={prettyLemma}/> </div>] else #[]
  let lemmaType ← match rw.name with
    | .const name => (·.type) <$> getConstInfo name
    | .fvar fvarId => inferType (.fvar fvarId)
  return {
    filtered := ← if !rw.isRefl && !rw.makesNewMVars then (some <$> html false) else pure none
    unfiltered := ← html true
    info := rw.info
    pattern := ← pattern lemmaType
  }
where
  /-- Render the matching side of the rewrite lemma.
  This is shown at the header of each section of rewrite results. -/
  pattern (type : Expr) : MetaM CodeWithInfos := withReducible do
    forallTelescopeReducing type fun _ e => do
      let .app (.app _ lhs) rhs := (← instantiateMVars e).cleanupAnnotations
        | throwError "Expected relation, not {indentExpr e}"
      ppExprTagged <| if rw.symm then rhs else lhs

/-- `generateSuggestion` is called in parallel for all rewrite lemmas.
- If the lemma succeeds, return a `RwResult`.
- If the lemma fails, return `none`
- If the attempt throws an error, return the error as `Html`.

Note: we use two `try`-`catch` clauses, because we rely on `ppConstTagged`
in the first `catch` branch, which could (in principle) throw an error again.
-/
def generateSuggestion (expr : Expr) (pasteInfo : RwPasteInfo) (gpos : GRewritePos)
    (pos : ExprWithPos) (lem : GRewriteLemma) : MetaM <| Task (Except Html <| Option RwResult) := do
  BaseIO.asTask <| EIO.catchExceptions (← dropM do withCurrHeartbeats do
    have : MonadExceptOf _ MetaM := MonadAlwaysExcept.except
    try .ok <$> withNewMCtxDepth do
      Core.checkSystem "infoview_search"
      let some rewrite ← checkGRewrite lem expr gpos pos | return none
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

def updateSectionState (s : SectionState) : MetaM (Array Html × SectionState) := do
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
def renderSection (filter : Bool) (s : SectionState) : Option Html := do
  let head ← s.results[0]?
  let suffix := match s.kind with
    | .hypothesis => " (local hypotheses)"
    | .fromFile => " (lemmas from current file)"
    | .fromCache => ""
  let suffix := if s.pending.isEmpty then suffix else suffix ++ " ⏳"
  let htmls := if filter then s.results.filterMap (·.filtered) else s.results.map (·.unfiltered)
  guard (!htmls.isEmpty)
  return mkListElement htmls
    <span> grw: <InteractiveCode fmt={head.pattern}/> {.text suffix} </span>

end InfoviewSearch.Grw
