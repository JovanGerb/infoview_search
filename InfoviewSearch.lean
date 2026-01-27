module

public import InfoviewSearch.Search.TryCandidates
public import InfoviewSearch.Tactics
public import InfoviewSearch.Unfold
public meta import Mathlib.Lean.Meta.KAbstractPositions


meta section

namespace InfoviewSearch
open Lean Meta Server Widget ProofWidgets Jsx


open RefreshComponent

def render (parts : Array Html) : Html :=
  if parts.isEmpty then
    .text "infoview_search found no suggestions"
  else
    .element "div" #[] parts

def viewKAbstractSubExpr' {α} (e : Expr) (pos : SubExpr.Pos)
    (k : Expr → LOption Nat → MetaM α) : MetaM α := do
  if let some (subExpr, occ) ← withReducible <| viewKAbstractSubExpr e pos then
    k subExpr occ.toLOption
  else
    Meta.viewSubexpr (fun _ e ↦ k e .undef) pos e

public def generateSuggestions (loc : SubExpr.GoalsLocation) (pasteInfo : PasteInfo)
    (parentDecl? : Option Name) (token : RefreshToken) : MetaM Unit := do
  let decl ← loc.mvarId.getDecl
  let lctx := decl.lctx |>.sanitizeNames.run' {options := (← getOptions)}
  Meta.withLCtx lctx decl.localInstances do
  let mut result : Array Html := #[]
  if let some html ← renderTactic loc pasteInfo then
    result := result.push html
  let (fvarId?, pos) ← match loc.loc with
    | .hypType fvarId pos  => pure (some fvarId, pos)
    | .target pos => pure (none, pos)
    | _ => token.refresh (render result); return
  let rootExpr ← instantiateMVars <| ← match fvarId? with
    | some fvarId => fvarId.getType
    | none => pure decl.type
  -- TODO: instead of computing the occurrences a single time (i.e. the `n` in `nth_rw n`),
  -- compute the occurrence for each suggestion separately, to avoid inaccuracies.
  viewKAbstractSubExpr' rootExpr pos fun subExpr occ ↦ do
  unless ← kabstractIsTypeCorrect rootExpr subExpr pos do
    token.refresh <| .text "infoview_search: the selected expression cannot be rewritten, \
      because the motive is not type correct. \
      This usually occurs when trying to rewrite a term that appears as a dependent argument."
    return
  let hyp? ← fvarId?.mapM (·.getUserName)
  let mut result := result
  if let some html ← InteractiveUnfold.renderUnfolds subExpr occ hyp? pasteInfo then
    result := result.push html
  let token' ← RefreshToken.new <| .text "searching for applicable lemmas"
  result := result.push <| <RefreshComponent state={← WithRpcRef.mk token'.ref}/>
  token.refresh (render result)
  do
    let ppSubExpr ← Widget.ppExprTagged subExpr
    let subExpr := { expr := subExpr, pos := pos }
    let state ← initializeWidgetState rootExpr subExpr pasteInfo occ fvarId? parentDecl?
    state.repeatRefresh ppSubExpr token'

@[server_rpc_method]
public def rpc (props : CancelPanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let some loc := props.selectedLocations.back? | return .text ""
  let doc ← RequestM.readDoc
  if loc.loc matches .hypValue .. then
    return .text "infoview_search cannot suggest anything about the value of a let variable."
  let some onGoal := props.goals.findFinIdx? (·.mvarId == loc.mvarId) |
    return .text "infoview_search: please reload the tactic state"
  let goal := props.goals[onGoal]
  let onGoal := guard (onGoal.val != 0) *> some onGoal.val
  let some goalsAt := (FileWorker.findGoalsAt? doc (doc.meta.text.lspPosToUtf8Pos props.pos)).get |
    return .text "Internal infoview_search error: could not find any goal at the cursor position"
  let some { ctxInfo := { parentDecl?, .. }, tacticInfo := { stx, .. }, .. } :=
    goalsAt.find? fun { useAfter, tacticInfo, .. } ↦
      let goals := if useAfter then tacticInfo.goalsAfter else tacticInfo.goalsBefore
      goals.contains loc.mvarId
    | return .text "infoview_search: Please reload the tactic state"
  let pasteInfo : PasteInfo := { «meta» := doc.meta, cursorPos := props.pos, onGoal, stx }
  goal.ctx.val.runMetaM {} do
  mkCancelRefreshComponent props.cancelTkRef.val (.text "searching for suggestions..") <|
    generateSuggestions loc pasteInfo parentDecl?

/-- The component called by the `#infoview_search` command. -/
@[widget_module]
public def infoviewSearchComponent : Component CancelPanelWidgetProps :=
  mk_rpc_widget% rpc

elab "#infoview_search" : command => do
  Elab.Command.liftCoreM do
    computeImportDiscrTrees { rw := true, grw := true, app := true, appAt := true }
    addPanelWidgetLocal <| ← mkCancelPanelWidget infoviewSearchComponent

end InfoviewSearch
