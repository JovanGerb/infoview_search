module

public import InfoviewSearch.Search.TryCandidates
public import InfoviewSearch.Tactics
public import InfoviewSearch.NormTactics
public import InfoviewSearch.Unfold
public meta import Mathlib.Lean.Meta.KAbstractPositions


meta section

namespace InfoviewSearch
open Lean Meta Server Widget ProofWidgets Jsx


open RefreshComponent

def viewKAbstractSubExpr' {m α}
    [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadError m]
    (e : Expr) (pos : SubExpr.Pos) (k : Expr → RwKind → m α) : m α := do
  if let some (subExpr, occ) ← withReducible <| viewKAbstractSubExpr e pos then
    let tpCorrect ← kabstractIsTypeCorrect e subExpr pos
    k subExpr (.valid tpCorrect occ)
  else
    Meta.viewSubexpr (fun _ e ↦ k e .hasBVars) pos e

def mkElabContextInfo : MetaM Elab.ContextInfo :=
  return {
    env           := (← getEnv)
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    fileMap       := default
    ngen          := (← getNGen)
  }

set_option linter.style.emptyLine false

public def generateSuggestions (loc : SubExpr.GoalsLocation)
    (parentDecl? : Option Name) (token : RefreshToken) : InfoviewSearchM Unit := do
  let decl ← loc.mvarId.getDecl
  -- TODO: decide whether we need this name sanitation
  let lctx := decl.lctx |>.sanitizeNames.run' {options := (← getOptions)}
  Meta.withLCtx lctx decl.localInstances do
  let mut htmls : Array Html := #[]
  if let some html ← renderTactic loc then
    htmls := htmls.push html
  let (fvarId?, pos) ← match loc.loc with
    | .hypType fvarId pos  => pure (some fvarId, pos)
    | .target pos => pure (none, pos)
    | _ => token.refresh (.element "div" #[] htmls); return
  let rootExpr ← instantiateMVars <| ← match fvarId? with
    | some fvarId => fvarId.getType
    | none => pure decl.type
  -- TODO: instead of computing the occurrences a single time (i.e. the `n` in `nth_rw n`),
  -- compute the occurrence for each suggestion separately, to avoid inaccuracies.
  viewKAbstractSubExpr' rootExpr pos fun subExpr rwKind ↦ do
  let hyp? ← fvarId?.mapM (·.getUserName)
  let mut htmls := htmls
  let convPath? ←
    if pos.isRoot then pure none else some <$> Conv.Path.ofSubExprPosArray rootExpr pos.toArray
  let rewritingInfo := { hyp?, convPath?, ctx := ← mkElabContextInfo }

  -- Presumably we should think better about which order to put these suggestions in.
  htmls := htmls.push (← suggestPush subExpr rewritingInfo)
  htmls := htmls.push (← suggestSimp subExpr rewritingInfo)
  htmls := htmls.push (← suggestNormCast subExpr rewritingInfo)
  htmls := htmls.push (← suggestAlgebraicNormalization subExpr rewritingInfo)
  if let some html ← InteractiveUnfold.renderUnfolds subExpr rwKind hyp? then
    htmls := htmls.push html

  let (searchHtml, token') ← mkRefreshComponent <| .text "searching for applicable lemmas"
  htmls := htmls.push searchHtml
  token.refresh (.element "div" #[] htmls)

  let ppSubExpr ← Widget.ppExprTagged subExpr
  let state ← initializeWidgetState rootExpr subExpr pos rwKind fvarId? parentDecl?
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
  let (statusHtml, statusToken) ← mkRefreshComponent
  let ctx := {
    onGoal, stx, statusToken
    «meta» := doc.meta
    cursorPos := props.pos
    computations := ← IO.mkRef ∅
    }
  let result ←  goal.ctx.val.runMetaM {} do
    (mkCancelRefreshComponent props.cancelTkRef.val (.text "searching for suggestions..") <|
      generateSuggestions loc parentDecl?).run ctx
  return <details «open»={true}>
    <summary className="mv2 pointer">
      infoview_search suggestions: {statusHtml}
    </summary>
    {result}
  </details>


/-- The component called by the `#infoview_search` command. -/
@[widget_module]
public def infoviewSearchComponent : Component CancelPanelWidgetProps :=
  mk_rpc_widget% rpc

elab "#infoview_search" : command => do
  Elab.Command.liftCoreM do
    computeImportDiscrTrees { rw := true, grw := true, app := true, appAt := true }
    addPanelWidgetLocal <| ← mkCancelPanelWidget infoviewSearchComponent

end InfoviewSearch
