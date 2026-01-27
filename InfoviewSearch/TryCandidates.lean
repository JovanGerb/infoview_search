module

public import InfoviewSearch.FindCandidates
public import InfoviewSearch.RefreshComponent
public import ProofWidgets.Component.FilterDetails

/-!
# A widget for showing library search results
-/

meta section

namespace InfoviewSearch
open Lean Widget ProofWidgets Jsx

inductive Candidates where
  | rw (hyp? : Option Name) (arr : Array Rw.RewriteLemma)
  | grw (hyp? : Option Name) (arr : Array Grw.GRewriteLemma)
  | app (arr : Array Apply.ApplyLemma)
  | appAt (hyp : Name) (arr : Array ApplyAt.ApplyAtLemma)

def getImportCandidates (rootExpr : Expr) (subExpr : SubExpr) (gpos : Array Grw.GRewritePos)
    (hyp? : Option Name) : MetaM (Array Candidates) := do
  let mut cands : Std.TreeMap _ _ _ := {}
  /- The order in which we show the suggestions for the same pattern for different tactics
  depends on the following insertion order.
  We choose the order `grw` => `rw` => `apply(at)`. -/
  if !gpos.isEmpty then
    cands := cands.mergeWith (fun _ ↦ (· ++ ·)) <|
      (← getImportMatches grwRef subExpr.expr).elts.map fun _ ↦ (·.map (.grw hyp?))
  cands := cands.mergeWith (fun _ ↦ (· ++ ·)) <|
    (← getImportMatches rwRef subExpr.expr).elts.map fun _ ↦ (·.map (.rw hyp?))
  if subExpr.pos == .root then
    if let some hyp := hyp? then
      cands := cands.mergeWith (fun _ ↦ (· ++ ·)) <|
        (← getImportMatches appAtRef rootExpr).elts.map fun _ ↦ (·.map (.appAt hyp))
    else
      cands := cands.mergeWith (fun _ ↦ (· ++ ·)) <|
        (← getImportMatches appRef rootExpr).elts.map fun _ ↦ (·.map .app)
  return cands.foldr (init := #[]) fun _ val acc ↦ acc ++ val

def getCandidates (rootExpr : Expr) (subExpr : SubExpr) (gpos : Array Grw.GRewritePos)
    (hyp? : Option Name) (pres : PreDiscrTrees) : MetaM (Array Candidates) := do
  let mut cands : Std.TreeMap _ _ _ := {}
  if !gpos.isEmpty then
    cands := cands.mergeWith (fun _ ↦ (· ++ ·)) <|
      (← getMatches pres.grw.toRefinedDiscrTree subExpr.expr).elts.map fun _ ↦ (·.map (.grw hyp?))
  cands := cands.mergeWith (fun _ ↦ (· ++ ·)) <|
    (← getMatches pres.rw.toRefinedDiscrTree subExpr.expr).elts.map fun _ ↦ (·.map (.rw hyp?))
  if subExpr.pos == .root then
    if let some hyp := hyp? then
      cands := cands.mergeWith (fun _ ↦ (· ++ ·)) <|
        (← getMatches pres.appAt.toRefinedDiscrTree rootExpr).elts.map fun _ ↦ (·.map (.appAt hyp))
    else
      cands := cands.mergeWith (fun _ ↦ (· ++ ·)) <|
        (← getMatches pres.app.toRefinedDiscrTree rootExpr).elts.map fun _ ↦ (·.map .app)
  return cands.foldr (init := #[]) fun _ val acc ↦ acc ++ val

public inductive SectionsState where
  | rw (s : SectionState Rw.ResultId)
  | grw (s : SectionState Grw.ResultId)
  | app (s : SectionState Apply.ResultId)
  | appAt (s : SectionState ApplyAt.ResultId)

def SectionsState.isFinished : SectionsState → Bool
  | .rw s | .grw s | .app s | .appAt s => s.pending.isEmpty

def SectionsState.hasProgressed : SectionsState → BaseIO Bool
  | .rw s | .grw s | .app s | .appAt s => s.pending.anyM IO.hasFinished

private def Candidates.generateSuggestions (rootExpr : Expr) (subExpr : SubExpr)
    (pasteInfo : PasteInfo) (occ : LOption Nat)
    (kind : PremiseKind) (gpos : Array Grw.GRewritePos) :
    Candidates → MetaM SectionsState
  | .rw hyp? arr => do
    let arr ← arr.mapM (Rw.generateSuggestion rootExpr subExpr pasteInfo hyp? occ)
    return .rw { kind, results := #[], pending := arr }
  | .grw hyp? arr => do
    if gpos.isEmpty then
      return .grw { kind, results := #[], pending := #[]}
    let arr ← arr.mapM (Grw.generateSuggestion rootExpr subExpr pasteInfo gpos hyp? occ)
    return .grw { kind, results := #[], pending := arr }
  | app arr => do
    let arr ← arr.mapM (Apply.generateSuggestion rootExpr pasteInfo)
    return .app { kind, results := #[], pending := arr }
  | appAt hyp arr => do
    let arr ← arr.mapM (ApplyAt.generateSuggestion rootExpr pasteInfo hyp)
    return .appAt { kind, results := #[], pending := arr }

/-- While the suggestions are computed, `WidgetState` is used to keep track of the progress.
Initially, it contains a bunch of unfinished `Task`s, and with each round of `updateWidgetState`,
the finished tasks are stored as results in each `SectionsState`. -/
public structure WidgetState where
  /-- The states of the sections in the widget. -/
  sections : Array SectionsState
  /-- The sections corresponding to imported theorems. These are in a separate task, because
  they may take a long time to evaluate. Once evaluated, these are appended to `sections`. -/
  importTask? : Option (Task (Except Exception <| Array SectionsState))
  /-- The errors that appeared in evaluating . -/
  exceptions : Array Html
  /-- The HTML shown at the drop-down above the suggestions. -/
  header : Html

set_option linter.style.emptyLine false in
public def initializeWidgetState (rootExpr : Expr) (subExpr : SubExpr) (pasteInfo : PasteInfo)
    (occ : LOption Nat) (fvarId? : Option FVarId) (parentDecl? : Option Name) :
    MetaM WidgetState := do
  Core.checkSystem "infoview_search"
  let mut sections := #[]

  let gpos ← Grw.getGRewritePos? rootExpr subExpr fvarId?.isSome
  let choice : Choice := {
    rw := true
    grw := !gpos.isEmpty
    app := subExpr.pos == .root && fvarId?.isNone
    appAt := subExpr.pos == .root && fvarId?.isSome
  }
  let pres ← computeLCtxDiscrTrees choice fvarId?
  let hyp? ← fvarId?.mapM (·.getUserName)
  Core.checkSystem "infoview_search"
  for cand in ← getCandidates rootExpr subExpr gpos hyp? pres do
    sections := sections.push
      (← cand.generateSuggestions rootExpr subExpr pasteInfo occ .hypothesis gpos)

  let pres ← computeModuleDiscrTrees choice parentDecl?
  Core.checkSystem "infoview_search"
  for cand in ← getCandidates rootExpr subExpr gpos hyp? pres do
    sections := sections.push
      (← cand.generateSuggestions rootExpr subExpr pasteInfo occ .fromFile gpos)

  Core.checkSystem "infoview_search"
  let importTask? := some <| ← EIO.asTask <| ← dropM (m := MetaM) do
    computeImportDiscrTrees choice
    (← getImportCandidates rootExpr subExpr gpos hyp?).mapM
      (·.generateSuggestions rootExpr subExpr pasteInfo occ .fromImport gpos)

  return {
    sections, importTask?, exceptions := #[]
    header :=
      <span> Lemma suggestions for <InteractiveCode fmt={← ppExprTagged subExpr.expr}/>: </span> }

/-- If `state.importTask?` has been evaluated, append the result to `section`. -/
def updateImportTask (state : WidgetState) : EIO Exception WidgetState := do
  if let some importTask := state.importTask? then
    if ← IO.hasFinished importTask then
      let sections ← EIO.ofExcept importTask.get
      return { state with importTask? := none, sections := state.sections ++ sections }
  return state

/-- Look at all of the pending `Task`s and if any of them gave a result, add this to the state. -/
def updateWidgetState (state : WidgetState) : MetaM WidgetState := do
  let state ← updateImportTask state
  let mut sections := #[]
  let mut exceptions := state.exceptions
  for s in state.sections do
    match s with
    | .rw s =>
      let (exs, s) ← s.update (·.isDuplicate ·)
      sections := sections.push <| .rw s
      exceptions := exceptions ++ exs
    | .grw s =>
      let (exs, s) ← s.update (·.isDuplicate ·)
      sections := sections.push <| .grw s
      exceptions := exceptions ++ exs
    | .app s =>
      let (exs, s) ← s.update (·.isDuplicate ·)
      sections := sections.push <| .app s
      exceptions := exceptions ++ exs
    | .appAt s =>
      let (exs, s) ← s.update (·.isDuplicate ·)
      sections := sections.push <| .appAt s
      exceptions := exceptions ++ exs
  return { state with sections, exceptions }

public def WidgetState.render (state : WidgetState)
    (ppSubExpr : CodeWithInfos) : Html :=
  <FilterDetails
    summary={state.header}
    all={go false state ppSubExpr}
    filtered={go true state ppSubExpr}
    initiallyFiltered={true} />
where
  /-- Render all of the sections of lemma suggestions -/
  go (filter : Bool) (state : WidgetState)
      (ppSubExpr : CodeWithInfos) : Html :=
    let htmls := state.sections.filterMap fun
      | .rw s => s.render filter "rw"
      | .grw s => s.render filter "grw"
      | .app s => s.render filter "apply"
      | .appAt s => s.render filter "apply at"
    let htmls := if state.importTask?.isNone then htmls else
      htmls.push <| .text "Imported theorems are being loaded..."
    let htmls := match renderExceptions state.exceptions with
      | some html => htmls.push html
      | none => htmls
    if htmls.isEmpty then
      <p> No lemma suggestions found for <InteractiveCode fmt={ppSubExpr}/> </p>
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

/-- Repeatedly run `updateWidgetState` until there is an update, and then return the result. -/
public partial def WidgetState.repeatRefresh (state : WidgetState)
    (ppSubExpr : CodeWithInfos) (token : RefreshToken) : MetaM Unit := do
  -- If there is nothing to compute, return the final (empty) display
  token.refresh (state.render ppSubExpr)
  let mut state := state
  while !state.sections.all (·.isFinished) || state.importTask?.isSome do
    Core.checkSystem "infoview_search"
    -- Wait until some task has finished
    while !(← liftM <| state.sections.anyM (·.hasProgressed) <||> match state.importTask? with
        | none => pure false | some importTask => IO.hasFinished importTask) do
      IO.sleep 10
      Core.checkSystem "infoview_search"
    state ← updateWidgetState state
    token.refresh (state.render ppSubExpr)

end InfoviewSearch
