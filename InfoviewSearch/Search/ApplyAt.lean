module

public import InfoviewSearch.Search.SectionState
public import Mathlib.Tactic.ApplyAt

public meta section

namespace InfoviewSearch.ApplyAt
open Lean Meta Widget Server ProofWidgets Jsx

structure ApplyAtLemma where
  name : Premise

structure ResultId where
  numGoals : Nat
  nameLenght : Nat
  replacementSize : Nat
  name : String
  newGoals : Array AbstractMVarsResult
deriving Inhabited

/-- A apply lemma that has been applied to an expression. -/
structure Application extends ApplyAtLemma where
  /-- The proof of the application -/
  proof : Expr
  /-- The replacement expression obtained from the rewrite -/
  replacement : Expr
  /-- The extra goals created by the application -/
  newGoals : Array (MVarId × BinderInfo)
  /-- Whether any of the new goals contain another a new metavariable -/
  makesNewMVars : Bool
  info : ResultId
  hyp : Name

set_option linter.style.emptyLine false in
/-- If `thm` can be used to apply to `target`, return the applications. -/
def checkApplication (lem : ApplyAtLemma) (target : Expr) (hyp : Name) :
    MetaM Application := do
  let (proof, mvars, binderInfos, replacement) ← lem.name.forallMetaTelescopeReducing
  let assume ← inferType mvars.back!
  let mvars := mvars.pop
  unless ← isDefEq assume target do throwError "{assume} does not unify with {target}"
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
  let proof ← instantiateMVars proof
  let info := {
    numGoals := newGoals.size
    nameLenght := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr (← g.1.getType)).pretty.length + s
    name := lem.name.toString
    newGoals := ← newGoals.mapM fun g => do abstractMVars (← g.1.getType)
  }
  return { lem with proof, replacement, newGoals, makesNewMVars, info, hyp }

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
  -- let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab app.proof)
  `(tactic| apply $(mkIdent (← app.name.unresolveName)) at $(mkIdent app.hyp))

set_option linter.style.emptyLine false in
/-- Construct the `Result` from an `Application`. -/
def Application.toResult (app : Application) (pasteInfo : PasteInfo) :
    MetaM (Result ResultId) := do
  let tactic ← tacticSyntax app
  let replacement ← ppExprTagged app.replacement
  let mut newGoals := #[]
  for (mvarId, bi) in app.newGoals do
    -- TODO: think more carefully about which goals should be displayed
    -- Are there lemmas where a hypothesis is marked as implicit,
    -- which we would still want to show as a new goal?
    if bi.isExplicit then
      newGoals := newGoals.push (← ppExprTagged (← mvarId.getType))
  let mut htmls := #[<InteractiveCode fmt={replacement}/>]
  for newGoal in newGoals do
    htmls := htmls.push
      <div> <strong className="goal-vdash">⊢ </strong> <InteractiveCode fmt={newGoal}/> </div>
  let filtered ←
    if !app.makesNewMVars then
      some <$> mkSuggestion tactic pasteInfo (.element "div" #[] htmls)
    else
      pure none
  htmls := htmls.push (← app.name.toHtml)
  let unfiltered ← mkSuggestion tactic pasteInfo (.element "div" #[] htmls)
  let pattern ← forallTelescopeReducing (← app.name.getType) fun xs _ => do
    ppExprTagged (← inferType xs.back!)
  return { filtered, unfiltered, info := app.info, pattern }

/-- `generateSuggestion` is called in parallel for all apply lemmas. -/
def generateSuggestion (expr : Expr) (pasteInfo : PasteInfo) (hyp : Name) (lem : ApplyAtLemma) :
    MetaM (Result ResultId) :=
  withReducible do withNewMCtxDepth do
  let app ← checkApplication lem expr hyp
  app.toResult pasteInfo

end InfoviewSearch.ApplyAt
