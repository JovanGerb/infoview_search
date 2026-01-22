module

public import InfoviewSearch.Apply
public import InfoviewSearch.Rewrite
public import InfoviewSearch.GRewrite
public import InfoviewSearch.ApplyAt
public import InfoviewSearch.Tactics
public meta import Mathlib.Lean.GoalsLocation
public meta import Mathlib.Lean.Meta.KAbstractPositions
public import ProofWidgets.Component.FilterDetails


public meta section

namespace InfoviewSearch
open Lean Meta Server Widget ProofWidgets Jsx Mathlib Tactic RefinedDiscrTree

inductive SectionState where
  | rw (s : Rw.SectionState)
  | grw (s : Grw.SectionState)
  | apply (s : Apply.SectionState)
  | applyAt (s : ApplyAt.SectionState)

def SectionState.isFinished : SectionState → Bool
  | .rw s => s.pending.isEmpty
  | .grw s => s.pending.isEmpty
  | .apply s => s.pending.isEmpty
  | .applyAt s => s.pending.isEmpty

def SectionState.hasProgressed : SectionState → BaseIO Bool
  | .rw s => s.pending.anyM IO.hasFinished
  | .grw s => s.pending.anyM IO.hasFinished
  | .apply s => s.pending.anyM IO.hasFinished
  | .applyAt s => s.pending.anyM IO.hasFinished

/-- While the suggestions are computed, `WidgetState` is used to keep track of the progress.
Initially, it contains a bunch of unfinished `Task`s, and with each round of `updateWidgetState`,
the finished tasks are stored as results in each `SectionState`. -/
structure WidgetState where
  /-- The states of the sections in the widget. -/
  sections : Array SectionState
  /-- The errors that appeared in evaluating . -/
  exceptions : Array Html
  /-- The HTML shown at the top of the suggestions. -/
  header : Html

/-- Look a all of the pending `Task`s and if any of them gave a result, add this to the state. -/
def updateWidgetState (state : WidgetState) : MetaM WidgetState := do
  let mut sections := #[]
  let mut exceptions := state.exceptions
  for s in state.sections do
    match s with
    | .rw s =>
      let (exs, s) ← Rw.updateSectionState s
      sections := sections.push <| .rw s
      exceptions := exceptions ++ exs
    | .grw s =>
      let (exs, s) ← Grw.updateSectionState s
      sections := sections.push <| .grw s
      exceptions := exceptions ++ exs
    | .apply s =>
      let (exs, s) ← Apply.updateSectionState s
      sections := sections.push <| .apply s
      exceptions := exceptions ++ exs
    | .applyAt s =>
      let (exs, s) ← ApplyAt.updateSectionState s
      sections := sections.push <| .applyAt s
      exceptions := exceptions ++ exs
  return { state with sections, exceptions }

def renderWidget (state : WidgetState) (pre : Array Html) (rewriteTarget : CodeWithInfos) : Html :=
  <FilterDetails
    summary={state.header}
    all={render false state pre rewriteTarget}
    filtered={render true state pre rewriteTarget}
    initiallyFiltered={true} />
where
  /-- Render all of the sections of rewrite results -/
  render (filter : Bool) (state : WidgetState) (pre : Array Html)
      (rewriteTarget : CodeWithInfos) : Html :=
    let htmls := state.sections.filterMap fun
      | .rw s => Rw.renderSection filter s
      | .grw s => Grw.renderSection filter s
      | .apply s => Apply.renderSection filter s
      | .applyAt s => ApplyAt.renderSection filter s
    let htmls := pre ++ htmls
    let htmls := match renderExceptions state.exceptions with
      | some html => htmls.push html
      | none => htmls
    if htmls.isEmpty then
      <p> No suggestions found for <InteractiveCode fmt={rewriteTarget}/> </p>
    else
      .element "div" #[("style", json% {"marginLeft" : "4px"})] htmls
  /-- Render the error messages -/
  renderExceptions (exceptions : Array Html) : Option Html := do
    if exceptions.isEmpty then none else
    some <|
      <details «open»={true}>
        <summary className="mv2 pointer">
          <span «class»="error"> Error messages: </span>
        </summary>
        {Html.element "ul" #[("style", json% { "padding-left" : "30px"})] exceptions}
      </details>


private inductive Candidates where
  | rw (arr : Array Rw.RewriteLemma)
  | grw (arr : Array Grw.GRewriteLemma)
  | apply (arr : Array Apply.ApplyLemma)
  | applyAt (arr : Array ApplyAt.ApplyAtLemma)

private def Candidates.generateSuggestion (expr : Expr) (pasteInfo : RwPasteInfo)
    (kind : PremiseKind) (pos : ExprWithPos) (gpos : Option Grw.GRewritePos) :
    Candidates → MetaM SectionState
  | .rw arr => do
    let arr ← arr.mapM (Rw.generateSuggestion expr pasteInfo pos)
    return .rw { kind, results := #[], pending := arr }
  | .grw arr => do
    let some gpos := gpos | return .grw { kind, results := #[], pending := #[]}
    let arr ← arr.mapM (Grw.generateSuggestion expr pasteInfo gpos pos)
    return .grw { kind, results := #[], pending := arr }
  | .apply arr => do
    let arr ← arr.mapM (Apply.generateSuggestion expr pasteInfo.toPasteInfo)
    return .apply { kind, results := #[], pending := arr }
  | .applyAt arr => do
    let arr ← arr.mapM (ApplyAt.generateSuggestion expr pasteInfo)
    return .applyAt { kind, results := #[], pending := arr }

set_option linter.style.emptyLine false in
def initializeWidgetState (expr : Expr) (pasteInfo : RwPasteInfo)
    (pos : ExprWithPos) (exceptFVarId : Option FVarId) (parentDecl? : Option Name) :
    RefreshComponent.RefreshT MetaM WidgetState := do
  Core.checkSystem "infoview_search"
  let mut sections := #[]

  let gpos ← Grw.getGRewritePos? expr pos exceptFVarId.isSome

  Core.checkSystem "infoview_search"
  RefreshComponent.refresh <| .text "searching the local hypotheses.."
  let cands :=
    Std.TreeMap.mergeWith (fun _ a b => a ++ b)
      ((← Rw.getHypothesisCandidates expr exceptFVarId).elts.map
        fun _ => (·.map Candidates.rw)) <|
    Std.TreeMap.mergeWith (fun _ a b => a ++ b)
      ((← Grw.getHypothesisCandidates expr exceptFVarId gpos).elts.map
        fun _ => (·.map Candidates.grw)) <|
    Std.TreeMap.mergeWith (fun _ a b => a ++ b)
      ((← Apply.getHypothesisCandidates pos exceptFVarId).elts.map
        fun _ => (·.map Candidates.apply))
      ((← ApplyAt.getHypothesisCandidates pos exceptFVarId).elts.map
        fun _ => (·.map Candidates.applyAt))
  for (_, cand) in cands.toArray.reverse do
    for cand in cand do
      sections := sections.push (← cand.generateSuggestion expr pasteInfo .hypothesis pos gpos)

  Core.checkSystem "infoview_search"
  RefreshComponent.refresh <| .text "searching the lemmas from the current file.."
  let cand :=
    Std.TreeMap.mergeWith (fun _ a b => a ++ b)
      ((← Rw.getModuleCandidates expr parentDecl?).elts.map fun _ => (·.map Candidates.rw)) <|
    Std.TreeMap.mergeWith (fun _ a b => a ++ b)
      ((← Grw.getModuleCandidates expr parentDecl?).elts.map fun _ => (·.map Candidates.grw)) <|
    Std.TreeMap.mergeWith (fun _ a b => a ++ b)
      ((← Apply.getModuleCandidates expr parentDecl?).elts.map fun _ => (·.map Candidates.apply))
      ((← ApplyAt.getModuleCandidates expr parentDecl?).elts.map fun _ =>
        (·.map Candidates.applyAt))
  for (_, cand) in cand.toArray.reverse do
    for cand in cand do
      sections := sections.push (← cand.generateSuggestion expr pasteInfo .fromFile pos gpos)

  Core.checkSystem "infoview_search"
  RefreshComponent.refresh <| .text "searching the `rw` discrimination tree.."
  let mut cands := (← Rw.getImportCandidates expr).elts.map fun _ => (·.map Candidates.rw)

  if let some gpos := gpos then
    Core.checkSystem "infoview_search"
    RefreshComponent.refresh <| .text s!"searching the `grw` ({gpos.relName}) discrimination tree.."
    cands := Std.TreeMap.mergeWith (fun _ a b => a ++ b) cands <|
      (← Grw.getImportCandidates expr gpos).elts.map fun _ => (·.map Candidates.grw)

  Core.checkSystem "infoview_search"
  RefreshComponent.refresh <| .text "searching the `apply` discrimination tree.."
  cands := Std.TreeMap.mergeWith (fun _ a b => a ++ b) cands <|
    (← Apply.getImportCandidates pos exceptFVarId).elts.map fun _ => (·.map Candidates.apply)

  Core.checkSystem "infoview_search"
  RefreshComponent.refresh <| .text "searching the `apply at` discrimination tree.."
  cands := Std.TreeMap.mergeWith (fun _ a b => a ++ b) cands <|
    (← ApplyAt.getImportCandidates pos exceptFVarId).elts.map fun _ => (·.map Candidates.applyAt)

  Core.checkSystem "infoview_search"
  RefreshComponent.refresh <| .text "searching the lemmas.."
  for (_, cand) in cands.toArray.reverse do
    for cand in cand do
      sections := sections.push (← cand.generateSuggestion expr pasteInfo .fromCache pos gpos)

  return {
    sections, exceptions := #[]
    header := <span> Suggestions for <InteractiveCode fmt={← ppExprTagged expr}/>: </span> }

open RefreshComponent

/-- Repeatedly run `updateWidgetState` until there is an update, and then return the result. -/
partial def waitAndRefresh (state : WidgetState) (pre : Array Html)
    (rewriteTarget : CodeWithInfos) : RefreshT MetaM Unit := do
  -- If there is nothing to compute, return the final (empty) display
  refresh (renderWidget state pre rewriteTarget)
  let mut state := state
  while !state.sections.all (·.isFinished) do
    Core.checkSystem "infoview_search"
    -- Wait until some task has finished
    while !(← liftM <| state.sections.anyM (·.hasProgressed)) do
      IO.sleep 10
      Core.checkSystem "infoview_search"
    state ← updateWidgetState state
    refresh (renderWidget state pre rewriteTarget)

def generateSuggestions (loc : SubExpr.GoalsLocation) («meta» : DocumentMeta)
    (cursorPos : Lsp.Position) (onGoal : Option Nat) (stx : Syntax) (parentDecl? : Option Name) :
    RefreshT MetaM Unit := do
  let decl ← loc.mvarId.getDecl
  let lctx := decl.lctx |>.sanitizeNames.run' {options := (← getOptions)}
  Meta.withLCtx lctx decl.localInstances do
  let rootExpr ← loc.rootExpr
  -- TODO: instead of rejecting terms with bound variables, and rejecting terms with a bad motive,
  -- use `simp_rw` as the suggested tactic instead of `rw`.
  -- TODO: instead of computing the occurrences a single time (i.e. the `n` in `nth_rw n`),
  -- compute the occurrence for each suggestion separately, to avoid inaccuracies.
  let pos := { root := rootExpr, targetPos := loc.pos }
  let some (subExpr, occ) ← withReducible <| viewKAbstractSubExpr rootExpr loc.pos |
    refresh <| .text "infoview_search: expressions with bound variables are not yet supported"
  unless ← kabstractIsTypeCorrect rootExpr subExpr loc.pos do
    refresh <| .text "infoview_search: the selected expression cannot be rewritten, \
      because the motive is not type correct. \
      This usually occurs when trying to rewrite a term that appears as a dependent argument."
    return
  let location ← loc.fvarId?.mapM (·.getUserName)
  let pasteInfo :=
    { «meta», cursorPos, occ, hyp? := location, onGoal, stx }
  let state ← initializeWidgetState subExpr pasteInfo pos loc.fvarId? parentDecl?
  -- Computing the tactic suggestions is cheap enough that it doesn't need a separate thread.
  -- However, we do this after the parallel computations
  -- have already been spawned by `initializeWidgetState`.
  RefreshComponent.refresh <| .text "searching for applicable tactics.."
  let pre ← renderTactic subExpr occ location loc pasteInfo.toPasteInfo
  waitAndRefresh state pre (← ppExprTagged subExpr)

@[server_rpc_method]
def rpc (props : CancelPanelWidgetProps) : RequestM (RequestTask Html) :=
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
  let some { ctxInfo := { parentDecl?, .. }, tacticInfo := { stx, .. }, ..} :=
    goalsAt.find? fun { useAfter, tacticInfo, .. } ↦
      let goals := if useAfter then tacticInfo.goalsAfter else tacticInfo.goalsBefore
      goals.contains loc.mvarId
    | return .text "infoview_search: Please reload the tactic state"
  goal.ctx.val.runMetaM {} do
  mkCancelRefreshComponent props.cancelTkRef.val (.text "searching for suggestions..") <|
    generateSuggestions loc doc.meta props.pos onGoal stx parentDecl?

/-- The component called by the `rw!?` tactic -/
@[widget_module]
def infoviewSearchComponent : Component CancelPanelWidgetProps :=
  mk_rpc_widget% rpc


private def withTreeCtx (ctx : Core.Context) : Core.Context :=
  { ctx with maxHeartbeats := 0, diag := getDiag ctx.options }

set_option linter.style.emptyLine false in

elab "#infoview_search" : command => do
  have : Inhabited (IO.Ref (Option (RefinedDiscrTree Rw.RewriteLemma))) := ⟨← IO.mkRef none⟩
  let ref := Rw.importedRewriteLemmasExt.getState (← getEnv)
  if (← ref.get).isNone then
    let tree ← Elab.Command.liftCoreM do
      let ngen ← getNGen
      let (cNGen, ngen) := ngen.mkChild
      setNGen ngen
      withTheReader Core.Context withTreeCtx do
          createImportedDiscrTree cNGen (← getEnv) Rw.addRewriteEntry 5000 256
    ref.set tree

  have : Inhabited (IO.Ref (Option (RefinedDiscrTree Grw.GRewriteLemma))) := ⟨← IO.mkRef none⟩
  let ref := Rw.importedRewriteLemmasExt.getState (← getEnv)
  if (← ref.get).isNone then
    let tree ← Elab.Command.liftCoreM do
      let ngen ← getNGen
      let (cNGen, ngen) := ngen.mkChild
      setNGen ngen
      withTheReader Core.Context withTreeCtx do
          createImportedDiscrTree cNGen (← getEnv) Rw.addRewriteEntry 5000 256
    ref.set tree

  have : Inhabited (IO.Ref (Option (RefinedDiscrTree Apply.ApplyLemma))) := ⟨← IO.mkRef none⟩
  let ref := Apply.importedApplyLemmasExt.getState (← getEnv)
  if (← ref.get).isNone then
    let tree ← Elab.Command.liftCoreM do
      let ngen ← getNGen
      let (cNGen, ngen) := ngen.mkChild
      setNGen ngen
      withTheReader Core.Context withTreeCtx do
          createImportedDiscrTree cNGen (← getEnv) Apply.addApplyEntry 5000 256
    ref.set tree

  have : Inhabited (IO.Ref (Option (RefinedDiscrTree ApplyAt.ApplyAtLemma))) := ⟨← IO.mkRef none⟩
  let ref := ApplyAt.importedApplyLemmasExt.getState (← getEnv)
  if (← ref.get).isNone then
    let tree ← Elab.Command.liftCoreM do
      let ngen ← getNGen
      let (cNGen, ngen) := ngen.mkChild
      setNGen ngen
      withTheReader Core.Context withTreeCtx do
          createImportedDiscrTree cNGen (← getEnv) ApplyAt.addApplyAtEntry 5000 256
    ref.set tree

  let ref ← WithRpcRef.mk (← IO.mkRef (← IO.CancelToken.new))
  addPanelWidgetLocal {
    javascriptHash := infoviewSearchComponent.javascriptHash
    id := ``infoviewSearchComponent
    props := (return json% { cancelTkRef : $(← rpcEncode ref)}) }

end InfoviewSearch
