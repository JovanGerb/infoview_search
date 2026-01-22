/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
-/
module

public import Mathlib.Lean.Meta.RefinedDiscrTree
public import InfoviewSearch.RefreshComponent

/-!
# Point & click library rewriting

This file defines `rw!?`, an interactive tactic that suggests rewrites for any expression selected
by the user.

`rw!?` uses a (lazy) `RefinedDiscrTree` to lookup a list of candidate rewrite lemmas.
It excludes lemmas that are automatically generated.
Each lemma is then checked one by one to see whether it is applicable.
For each lemma that works, the corresponding rewrite tactic is constructed
and converted into a `String` that fits inside mathlib's 100 column limit,
so that it can be pasted into the editor when selected by the user.

The `RefinedDiscrTree` lookup groups the results by match pattern and gives a score to each pattern.
This is used to display the results in sections. The sections are ordered by this score.
Within each section, the lemmas are sorted by
- rewrites with fewer extra goals come first
- left-to-right rewrites come first
- shorter lemma names come first
- shorter replacement expressions come first (when taken as a string)
- alphabetically ordered by lemma name

The lemmas are optionally filtered to avoid duplicate rewrites, or trivial rewrites. This
is controlled by the filter button on the top right of the results.

When a rewrite lemma introduces new goals, these are shown after a `⊢`.

## TODO

Ways to improve `rw!?`:
- Improve the logic around `nth_rw` and occurrences,
  and about when to pass explicit arguments to the rewrite lemma.
  For example, we could only pass explicit arguments if that avoids using `nth_rw`.
  Performance may be a limiting factor for this.
  Currently, the occurrence is computed by `viewKAbstractSubExpr`.
- Modify the interface to allow creating a whole `rw [.., ..]` chain, without having to go into
  the editor in between. For this to work, we will need a more general syntax,
  something like `rw [..]??`, which would be pasted into the editor.
- We could look for rewrites of partial applications of the selected expression.
  For example, when clicking on `(f + g) x`, there should still be an `add_comm` suggestion.

Ways to extend `rw!?`:
- Support generalized rewriting (`grw`)
- Integrate rewrite search with the `calc?` widget so that a `calc` block can be created using
  just point & click.

-/

/-! ### Caching -/

public meta section

namespace InfoviewSearch.Rw

open Lean Meta RefinedDiscrTree

/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
structure RewriteLemma where
  /-- The lemma -/
  name : Premise
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool

/-- Return `true` if `s` and `t` are equal up to swapping the `MVarId`s. -/
def isMVarSwap (t s : Expr) : Bool :=
  go t s {} |>.isSome
where
  /-- The main loop of `isMVarSwap`. Returning `none` corresponds to a failure. -/
  go (t s : Expr) (swaps : List (MVarId × MVarId)) : Option (List (MVarId × MVarId)) := do
  let isTricky e := e.hasExprMVar || e.hasLevelParam
  if isTricky t then
    guard (isTricky s)
    match t, s with
    -- Note we don't bother keeping track of universe level metavariables.
    | .const n₁ _       , .const n₂ _        => guard (n₁ == n₂); some swaps
    | .sort _           , .sort _            => some swaps
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => go d₁ d₂ swaps >>= go b₁ b₂
    | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _     => go d₁ d₂ swaps >>= go b₁ b₂
    | .mdata d₁ e₁      , .mdata d₂ e₂       => guard (d₁ == d₂); go e₁ e₂ swaps
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => go t₁ t₂ swaps >>= go v₁ v₂ >>= go b₁ b₂
    | .app f₁ a₁        , .app f₂ a₂         => go f₁ f₂ swaps >>= go a₁ a₂
    | .proj n₁ i₁ e₁    , .proj n₂ i₂ e₂     => guard (n₁ == n₂ && i₁ == i₂); go e₁ e₂ swaps
    | .fvar fvarId₁     , .fvar fvarId₂      => guard (fvarId₁ == fvarId₂); some swaps
    | .lit v₁           , .lit v₂            => guard (v₁ == v₂); some swaps
    | .bvar i₁          , .bvar i₂           => guard (i₁ == i₂); some swaps
    | .mvar mvarId₁     , .mvar mvarId₂      =>
      match swaps.find? (·.1 == mvarId₁) with
      | none =>
        guard (swaps.all (·.2 != mvarId₂))
        let swaps := (mvarId₁, mvarId₂) :: swaps
        if mvarId₁ == mvarId₂ then
          some swaps
        else
          some <| (mvarId₂, mvarId₁) :: swaps
      | some (_, mvarId) => guard (mvarId == mvarId₂); some swaps
    | _                 , _                  => none
  else
    guard (t == s); some swaps

/-- Extract the left and right hand sides of an equality or iff statement. -/
@[inline] def eqOrIff? (e : Expr) : Option (Expr × Expr) :=
  match e.eq? with
  | some (_, lhs, rhs) => some (lhs, rhs)
  | none => e.iff?

/-- Try adding the lemma to the `RefinedDiscrTree`. -/
def addRewriteEntry (name : Name) (cinfo : ConstantInfo) :
    MetaM (List (RewriteLemma × List (Key × LazyEntry))) := do
  -- we start with a fast-failing check to see if the lemma has the right shape
  let .const head _ := cinfo.type.getForallBody.getAppFn | return []
  unless head == ``Eq || head == ``Iff do return []
  setMCtx {} -- recall that the metavariable context is not guaranteed to be empty at the start
  let (_, _, eqn) ← forallMetaTelescope cinfo.type
  let some (lhs, rhs) := eqOrIff? eqn | return []
  if isBadMatch lhs then
    if isBadMatch rhs then
      return []
    else
      return [({ name := .const name, symm := true }, ← initializeLazyEntryWithEta rhs)]
  else
    let result := ({ name := .const name, symm := false }, ← initializeLazyEntryWithEta lhs)
    if isBadMatch rhs || isMVarSwap lhs rhs then
      return [result]
    else
      return [result, ({ name := .const name, symm := true }, ← initializeLazyEntryWithEta rhs)]


/-- Try adding the local hypothesis to the `RefinedDiscrTree`. -/
def addLocalRewriteEntry (decl : LocalDecl) :
    MetaM (List (RewriteLemma × List (Key × LazyEntry))) :=
  withReducible do
  let (_, _, eqn) ← forallMetaTelescopeReducing decl.type
  let some (lhs, rhs) := eqOrIff? (← whnf eqn) | return []
  return [
    ({ name := .fvar decl.fvarId, symm := false }, ← initializeLazyEntryWithEta lhs),
    ({ name := .fvar decl.fvarId, symm := true }, ← initializeLazyEntryWithEta rhs)]

initialize importedRewriteLemmasExt :
    EnvExtension (IO.Ref (Option (RefinedDiscrTree RewriteLemma))) ←
  registerEnvExtension (IO.mkRef none)

/-- Get all potential rewrite lemmas from the imported environment.
By setting the `librarySearch.excludedModules` option, all lemmas from certain modules
can be excluded. -/
def getImportCandidates (e : Expr) : MetaM (MatchResult RewriteLemma) := do
  findImportMatches importedRewriteLemmasExt addRewriteEntry
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
    MetaM (MatchResult RewriteLemma) := do
  let moduleTreeRef ← createModuleTreeRef fun name cinfo ↦
    if name == parentDecl? then return [] else addRewriteEntry name cinfo
  findModuleMatches moduleTreeRef e

/-- Construct the `RefinedDiscrTree` of all local hypotheses. -/
def getHypotheses (except : Option FVarId) : MetaM (RefinedDiscrTree RewriteLemma) := do
  let mut tree : PreDiscrTree RewriteLemma := {}
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && except.all (· != decl.fvarId) then
      for (val, entries) in ← addLocalRewriteEntry decl do
        for (key, entry) in entries do
          tree := tree.push key (entry, val)
  return tree.toRefinedDiscrTree

/-- Return all applicable hypothesis rewrites of `e`. Similar to `getImportCandidates`. -/
def getHypothesisCandidates (e : Expr) (except : Option FVarId) :
    MetaM (MatchResult RewriteLemma) := do
  let (candidates, _) ← (← getHypotheses except).getMatch e (unify := false) (matchRootStar := true)
  MonadExcept.ofExcept candidates



/-! ### Checking rewrite lemmas -/

structure RewriteInfo where
  numGoals : Nat
  symm : Bool
  nameLenght : Nat
  replacementSize : Nat
  name : String
  -- TODO: in this implementation, we conclude that two rewrites are the same if they
  -- rewrite into the same expression. But there can be two rewrites that have
  -- different side conditions!
  replacement : AbstractMVarsResult
deriving Inhabited

/-- A rewrite lemma that has been applied to an expression. -/
structure Rewrite extends RewriteLemma where
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
def checkRewrite (lem : RewriteLemma) (e : Expr) (pos : ExprWithPos) : MetaM (Option Rewrite) := do
  let thm ← match lem.name with
    | .const name => mkConstWithFreshMVarLevels name
    | .fvar fvarId => pure (.fvar fvarId)
  withTraceNodeBefore `infoview_suggest (return m!
    "rewriting {e} by {if lem.symm then "← " else ""}{thm}") do
  let (mvars, binderInfos, eqn) ← forallMetaTelescopeReducing (← inferType thm)
  let some (lhs, rhs) := eqOrIff? (← whnf eqn) | return none
  let (lhs, rhs) := if lem.symm then (rhs, lhs) else (lhs, rhs)
  let lhsOrig := lhs; let mctxOrig ← getMCtx
  let unifies ← withTraceNodeBefore `infoview_suggest (return m! "unifying {e} =?= {lhs}")
    (withReducible (isDefEq e lhs))
  unless unifies do return none
  -- just like in `kabstract`, we compare the `HeadIndex` and number of arguments
  let lhs ← instantiateMVars lhs
  -- TODO: if the `headIndex` doesn't match, then use `simp_rw` instead of `rw` in the suggestion,
  -- instead of just not showing the suggestion.
  if lhs.toHeadIndex != e.toHeadIndex || lhs.headNumArgs != e.headNumArgs then
    return none
  try synthAppInstances `infoview_suggest default mvars binderInfos false false
  catch _ => return none
  let mut extraGoals := #[]
  let mut justLemmaName := true
  for mvar in mvars, bi in binderInfos do
    unless ← mvar.mvarId!.isAssigned do
      if ← isProof mvar <&&> mvar.mvarId!.assumptionCore then
        justLemmaName := false
      else
        extraGoals := extraGoals.push (mvar.mvarId!, bi)

  let replacement ← instantiateMVars rhs
  let makesNewMVars ←
    pure (replacement.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome <||>
    extraGoals.anyM fun goal ↦ do
      let type ← instantiateMVars <| ← goal.1.getType
      return (type.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome
  let proof ← instantiateMVars (mkAppN thm mvars)
  let isRefl ← isExplicitEq e replacement
  if justLemmaName then
    justLemmaName ← withMCtx mctxOrig do kabstractFindsPositions lhsOrig pos
  let info := {
    numGoals := extraGoals.size
    symm := lem.symm
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
  (compare a.4 b.4).then <|
  (compare a.5 b.5)

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
  mkRewrite pasteInfo.occ rw.symm proof pasteInfo.hyp?

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
  let replacementString ← ppExprTagged rw.replacement
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
      #[<InteractiveCode fmt={replacementString}/>] ++ extraGoals ++
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
  pattern (type : Expr) : MetaM CodeWithInfos := do
    forallTelescopeReducing type fun _ e => do
      let some (lhs, rhs) := eqOrIff? (← whnf e)
        | throwError "Expected equation, not {indentExpr e}"
      ppExprTagged <| if rw.symm then rhs else lhs

/-- `generateSuggestion` is called in parallel for all rewrite lemmas.
- If the lemma succeeds, return a `RwResult`.
- If the lemma fails, return `none`
- If the attempt throws an error, return the error as `Html`.

Note: we use two `try`-`catch` clauses, because we rely on `ppConstTagged`
in the first `catch` branch, which could (in principle) throw an error again.
-/
def generateSuggestion (expr : Expr) (pasteInfo : RwPasteInfo) (pos : ExprWithPos)
    (lem : RewriteLemma) : MetaM <| Task (Except Html <| Option RwResult) := do
  BaseIO.asTask <| EIO.catchExceptions (← dropM do withCurrHeartbeats do
    have : MonadExceptOf _ MetaM := MonadAlwaysExcept.except
    try .ok <$> withNewMCtxDepth do
      Core.checkSystem "rw!?"
      let some rewrite ← checkRewrite lem expr pos | return none
      some <$> rewrite.toResult pasteInfo
    catch e => withCurrHeartbeats do
      return .error
        <li>
          An error occurred when processing rewrite lemma
          <InteractiveCode fmt={← ppPremiseTagged lem.name}/>:
          <br/>
          <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData} />
        </li>)
    fun e =>
      return .error
        <li>
          An error occurred when pretty printing rewrite lemma {.text lem.1.toString}:
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
  return mkListElement htmls <span> rw: <InteractiveCode fmt={head.pattern}/> {.text suffix} </span>

end InfoviewSearch.Rw
