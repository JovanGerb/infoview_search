module

public import InfoviewSearch.Search.TryCandidates
public import InfoviewSearch.Tactics
public import InfoviewSearch.NormTactics
public import InfoviewSearch.HypTactics
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

set_option linter.style.emptyLine false

public def generateSuggestions (loc : SubExpr.GoalsLocation)
    (parentDecl? : Option Name) (token : RefreshToken Html) : InfoviewSearchM Unit := do
  -- TODO: instead of just putting `✝` after inaccessible names,
  -- we should figure out how to use `rename_i` to actually refer to shadowed local variables.
  let lctx := (← getLCtx) |>.sanitizeNames.run' {options := (← getOptions)}
  Meta.withLCtx' lctx do
  let (fvarId?, pos) ← match loc.loc with
    | .hypType fvarId pos  => pure (some fvarId, pos)
    | .target pos => pure (none, pos)
    | .hyp fvarId =>
      if let some html ← suggestForHyp fvarId then
        token.set html
      else
        token.set <p> No suggestions found for hypothesis {← exprToHtml (.fvar fvarId)} </p>
      return
    | .hypValue .. =>
      token.set <| .text "internal infoview_search error: selected location is a `.hypValue`"
      return
  let rootExpr ← instantiateMVars <| ← match fvarId? with
    | some fvarId => fvarId.getType
    | none => loc.mvarId.getType
  -- TODO: instead of computing the occurrences a single time (i.e. the `n` in `nth_rw n`),
  -- compute the occurrence for each suggestion separately, to avoid inaccuracies.
  viewKAbstractSubExpr' rootExpr pos fun subExpr rwKind ↦ do
  let mut htmls : Array Html := #[]

  if let .fvar fvarId := subExpr.cleanupAnnotations then
    if let some html ← suggestForHyp fvarId then
      markProgress
      htmls := htmls.push html

  if let some html ← renderTactic then
    markProgress
    htmls := htmls.push html

  let rewritingInfo := {
    hyp? := ← fvarId?.mapM (·.getUserName)
    convPath? := ← if pos.isRoot then pure none else some <$> Conv.Path.ofSubExprPos rootExpr pos }
  -- We may want to think better about which order to put these suggestions in.
  htmls := htmls.push (← suggestPush subExpr rewritingInfo)
  htmls := htmls.push (← suggestSimp subExpr rewritingInfo)
  htmls := htmls.push (← suggestNormCast subExpr rewritingInfo)
  htmls := htmls.push (← suggestAlgebraicNormalization subExpr rewritingInfo)
  if let some html ← suggestUnfold subExpr rwKind then
    markProgress
    htmls := htmls.push html

  let (searchHtml, token') ← mkRefreshComponent (.text "") id
  htmls := htmls.push searchHtml
  token.set (.element "div" #[("style", json% {"marginLeft" : "4px"})] htmls)

  librarySearchSuggestions rootExpr subExpr rwKind parentDecl? token'

/-- If the set of computations is non-empty, display a `⏳` symbol with hover information that
shows all of the ongoing computations. -/
private def rerenderStatus (computations : Std.HashSet String) : Html :=
  if computations.isEmpty then
    .text ""
  else
    -- TODO: use a fancier throbber instead of `⏳`?
    let title := "ongoing searches: " ++ String.intercalate ", " computations.toList;
    <span title={title}> {.text "⏳"} </span>

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
  goal.ctx.val.runMetaM {} do loc.mvarId.withContext do
    let (statusHtml, statusToken) ← mkRefreshComponent ∅ rerenderStatus
    let targetHtml ← Meta.viewSubexpr (fun _ e ↦ exprToHtml e) loc.pos (← loc.rootExpr)
    let html ← mkCancelRefreshComponent props.cancelTkRef.val
      (.text "infoview_search has started searching.") fun masterToken ↦ do
      (generateSuggestions loc parentDecl? masterToken).run {
        onGoal, stx, masterToken, statusToken
        «meta» := doc.meta
        cursorPos := props.pos
        progress? := ← IO.mkRef false
        goal := loc.mvarId
        hyp? := loc.fvarId?
        pos := loc.pos
      }
    return <details «open»={true}>
      <summary className="mv2 pointer">
        infoview_search suggestions for {targetHtml}: {statusHtml}
      </summary>
      {html}
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
