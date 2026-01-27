module

public import InfoviewSearch.SectionState

public meta section

namespace InfoviewSearch.Apply
open Lean Meta Widget Server ProofWidgets Jsx

structure ApplyLemma where
  name : Premise

/-! ### Checking apply lemmas -/

structure ResultId where
  numGoals : Nat
  nameLenght : Nat
  replacementSize : Nat
  name : String
  newGoals : Array AbstractMVarsResult
deriving Inhabited

/-- A apply lemma that has been applied to an expression. -/
structure Application extends ApplyLemma where
  /-- The proof of the application -/
  proof : Expr
  /-- The extra goals created by the application -/
  newGoals : Array (MVarId × BinderInfo)
  /-- Whether any of the new goals contain another a new metavariable -/
  makesNewMVars : Bool
  info : ResultId

set_option linter.style.emptyLine false in
/-- If `thm` can be used to apply to `e`, return the applications. -/
def checkApplication (lem : ApplyLemma) (target : Expr) : MetaM (Option Application) := do
  let (proof, mvars, binderInfos, e) ← lem.name.forallMetaTelescopeReducing
  withTraceNodeBefore `infoview_search
    (return m!"applying {← lem.name.unresolveName} to {target}") do
  let unifies ← withTraceNodeBefore `infoview_search (return m! "unifying {e} =?= {target}")
    (withReducible (isDefEq e target))
  unless unifies do return none
  try synthAppInstances `infoview_search default mvars binderInfos false false
  catch _ => return none
  let mut newGoals := #[]
  for mvar in mvars, bi in binderInfos do
    unless ← mvar.mvarId!.isAssigned do
      newGoals := newGoals.push (mvar.mvarId!, bi)

  let makesNewMVars ← newGoals.anyM fun goal => do
    let type ← instantiateMVars <| ← goal.1.getType
    return (type.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome
  let proof ← instantiateMVars proof
  let info := {
    numGoals := newGoals.size
    nameLenght := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr (← g.1.getType)).pretty.length + s
    name := lem.name.toString
    newGoals := ← newGoals.mapM fun g => do abstractMVars (← g.1.getType)
  }
  return some { lem with proof, newGoals, makesNewMVars, info }

instance : Ord ResultId where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4)

def ResultId.isDuplicate (a b : ResultId) : MetaM Bool :=
  pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

/-- Return the `apply` tactic that performs the application. -/
def tacticSyntax (app : Application) : MetaM (TSyntax `tactic) := do
  let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab app.proof)
  if app.newGoals.isEmpty then
    `(tactic| exact $proof)
  else
    `(tactic| refine $proof)

set_option linter.style.emptyLine false in
/-- Construct the `Result` from an `Application`. -/
def Application.toResult (app : Application) (pasteInfo : PasteInfo) :
    MetaM (Result ResultId) := do
  let tactic ← tacticSyntax app
  let mut newGoals := #[]
  for (mvarId, bi) in app.newGoals do
    -- TODO: think more carefully about which goals should be displayed
    -- Are there lemmas where a hypothesis is marked as implicit,
    -- which we would still want to show as a new goal?
    if bi.isExplicit then
      newGoals := newGoals.push (← ppExprTagged (← mvarId.getType))
  let prettyLemma ← ppPremiseTagged app.name

  let html (showNames : Bool) :=
    mkSuggestionElement tactic pasteInfo (isText := newGoals.isEmpty) <|
      let newGoals := newGoals.map
        (<div> <strong className="goal-vdash">⊢ </strong> <InteractiveCode fmt={·}/> </div>)
      let newGoals := if newGoals.isEmpty then #[.text "Goal accomplished! 🎉"] else newGoals
      .element "div" #[] <| newGoals ++
        if showNames then #[<div> <InteractiveCode fmt={prettyLemma}/> </div>] else #[]
  let lemmaType ← match app.name with
    | .const name => (·.type) <$> getConstInfo name
    | .fvar fvarId => inferType (.fvar fvarId)
  return {
    filtered := ← if !app.makesNewMVars then (some <$> html false) else pure none
    unfiltered := ← html true
    info := app.info
    pattern := ← forallTelescope lemmaType fun _ e => ppExprTagged e
  }

/-- `generateSuggestion` is called in parallel for all apply lemmas.
- If the lemma succeeds, return a `Result AppInfo`.
- If the lemma fails, return `none`
- If the attempt throws an error, return the error as `Html`.

Note: we use two `try`-`catch` clauses, because we rely on `ppConstTagged`
in the first `catch` branch, which could (in principle) throw an error again.
-/
def generateSuggestion (expr : Expr) (pasteInfo : PasteInfo) (lem : ApplyLemma) :
    MetaM <| Task (Except Html <| Option (Result ResultId)) := do
  BaseIO.asTask <| EIO.catchExceptions (← dropM do withCurrHeartbeats do
    have : MonadExceptOf _ MetaM := MonadAlwaysExcept.except
    try .ok <$> withNewMCtxDepth do
      Core.checkSystem "infoview_search"
      let some app ← checkApplication lem expr | return none
      some <$> app.toResult pasteInfo
    catch e => withCurrHeartbeats do
      return .error
        <li>
          An error occurred when processing apply lemma
          <InteractiveCode fmt={← ppPremiseTagged lem.name}/>:
          <br/>
          <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData} />
        </li>)
    fun e =>
      return .error
        <li>
          An error occurred when pretty printing apply lemma {.text lem.1.toString}:
          <br/>
          <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData} />
        </li>

end InfoviewSearch.Apply
