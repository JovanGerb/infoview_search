/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Search.FindCandidates
public import InfoviewSearch.RefreshComponent
public import ProofWidgets.Component.FilterDetails

/-!
# A widget for showing library search results
-/

meta section

namespace InfoviewSearch
open Lean Server Widget ProofWidgets Jsx

inductive Candidates where
  | rw (i : RwInfo) (arr : Array RwLemma)
  | grw (i : GrwInfo) (arr : Array GrwLemma)
  | app (arr : Array ApplyLemma)
  | appAt (arr : Array ApplyAtLemma)

local instance {α β cmp} [Append β] : Append (Std.TreeMap α β cmp) :=
  ⟨.mergeWith fun _ ↦ (· ++ ·)⟩

open Meta.RefinedDiscrTree in
/-- Combine the results of looking up in various discrimination trees into an Array
of sections of candidates, where each section corresponds to one kind of match with the
discrimination tree. -/
@[inline]
def getCandidatesAux (rootExpr subExpr : Expr) (gpos : Array GrwPos) (rwKind : RwKind)
    (rw : Expr → MetaM (MatchResult RwLemma)) (grw : Expr → MetaM (MatchResult GrwLemma))
    (app : Expr → MetaM (MatchResult ApplyLemma)) (appAt : Expr → MetaM (MatchResult ApplyAtLemma))
    : InfoviewSearchM (Array Candidates) := do
  let mut cands : Std.TreeMap Nat (Array Candidates) := {}
  /- The order in which we show the suggestions for the same pattern for different tactics
  depends on the following insertion order.
  We choose the order `grw` => `rw` => `apply(at)`. -/
  if !gpos.isEmpty then
    cands := cands ++ (← grw subExpr).elts.map fun _ ↦ (·.map <|
      .grw { rootExpr, subExpr, rwKind, gpos })
  let mut rwExpr := subExpr
  let mut rwPos := (← read).pos
  repeat
    /- TODO: we are passing the same `rwKind` to each of these nested applications, but it is
    certainly possible that the correct `rwKind` is not the same for all of these.
    Though this edge case is probably very rare. -/
    cands := cands ++ (← rw rwExpr).elts.map fun _ ↦ (·.map (.rw <|
      { rootExpr, subExpr := rwExpr, pos := rwPos, rwKind }))
    match rwExpr with
    | .app f _ =>
      rwExpr := f
      rwPos := rwPos.pushAppFn
    | _ => break
  if (← read).pos == .root then
    if (← read).hyp?.isSome then
      cands := cands ++ (← appAt rootExpr).elts.map fun _ ↦ (·.map .appAt)
    else
      cands := cands ++ (← app rootExpr).elts.map fun _ ↦ (·.map .app)
  return cands.foldr (init := #[]) fun _ val acc ↦ acc ++ val

def getImportCandidates (rootExpr subExpr : Expr) (gpos : Array GrwPos)
    (rwKind : RwKind) : InfoviewSearchM (Array Candidates) :=
  getCandidatesAux rootExpr subExpr gpos rwKind
    (getImportMatches rwRef) (getImportMatches grwRef)
    (getImportMatches appRef) (getImportMatches appAtRef)

def getCandidates (rootExpr subExpr : Expr) (gpos : Array GrwPos)
    (rwKind : RwKind) (pres : PreDiscrTrees) : InfoviewSearchM (Array Candidates) :=
  getCandidatesAux rootExpr subExpr gpos rwKind
    (getMatches pres.rw.toRefinedDiscrTree) (getMatches pres.grw.toRefinedDiscrTree)
    (getMatches pres.app.toRefinedDiscrTree) (getMatches pres.appAt.toRefinedDiscrTree)

/-- Spawn a task that computes a piece of `Html` to be displayed when finished. -/
@[specialize]
def spawnTask {α} (premise : Premise) (k : InfoviewSearchM α) :
    InfoviewSearchM <| Task (Except Html (Option α)) := do
  let premiseHtml ← premise.toHtml
  let act ← dropM do
    /- Since this task may have been on the queue for a while,
    the first thing we do is check if it has been cancelled already. -/
    Core.checkInterrupted
    /- Each thread counts its own number of heartbeats, so it is important
    to use `withCurrHeartbeats` to avoid stray maxHeartbeats errors. -/
    withCurrHeartbeats do
      try
        return .ok (some (← k))
      catch ex =>
        /- By default, we catch the errors from failed lemma applications
        (appart from runtime exceptions, i.e. max heartbeats or max recursion depth,
        which aren't caught by the `try`-`catch` block).
        The `infoview_search.debug` option allows the user to still see all errors. -/
        if infoview_search.debug.get (← getOptions) then
          throw ex
        return .ok none
  BaseIO.asTask <| act.catchExceptions fun ex =>
    return .error <li>
        {premiseHtml} failed:
        <br/>
        <InteractiveMessage msg={← WithRpcRef.mk ex.toMessageData} />
      </li>

public inductive SectionsState where
  | rw (s : SectionState RwKey)
  | grw (s : SectionState GrwKey)
  | app (s : SectionState ApplyKey)
  | appAt (s : SectionState ApplyAtKey)

def SectionsState.isFinished : SectionsState → Bool
  | .rw s | .grw s | .app s | .appAt s => s.pending.isEmpty

def SectionsState.hasProgressed : SectionsState → BaseIO Bool
  | .rw s | .grw s | .app s | .appAt s => s.pending.anyM IO.hasFinished

def Candidates.generateSuggestions (source : Source) : Candidates → InfoviewSearchM SectionsState
  | .rw info arr => .rw <$>
    .new source <$> arr.mapM fun lem ↦ spawnTask lem.name <| lem.generateSuggestion info
  | .grw info arr => .grw <$>
    .new source <$> arr.mapM fun lem ↦ spawnTask lem.name <| lem.generateSuggestion info
  | .app arr => .app <$>
    .new source <$> arr.mapM fun lem ↦ spawnTask lem.name lem.generateSuggestion
  | .appAt arr => .appAt <$>
    .new source <$> arr.mapM fun lem ↦ spawnTask lem.name lem.generateSuggestion

/-- While the suggestions are computed, `WidgetState` is used to keep track of the progress.
Initially, it contains a bunch of unfinished `Task`s, and with each round of `updateWidgetState`,
the finished tasks are stored as results in each `SectionsState`. -/
public structure WidgetState where
  /-- The states of the sections in the widget. -/
  sections : Array SectionsState
  /-- The sections corresponding to imported theorems. These are in a separate task, because
  they may take a long time to evaluate. Once evaluated, these are appended to `sections`. -/
  importTask? : Option (Task (Except Exception <| Array SectionsState))
  /-- The HTML shown at the drop-down above the suggestions. -/
  header : Html

set_option linter.style.emptyLine false in
public def initializeWidgetState (rootExpr subExpr : Expr)
    (rwKind : RwKind) (parentDecl? : Option Name) :
    InfoviewSearchM WidgetState := do
  Core.checkSystem "infoview_search"
  let mut sections := #[]

  let pos := (← read).pos
  let fvarId? := (← read).hyp?
  let gpos ← getGrwPos? rootExpr subExpr pos fvarId?.isSome
  let choice : Choice := {
    rw := true
    grw := !gpos.isEmpty
    app := pos == .root && fvarId?.isNone
    appAt := pos == .root && fvarId?.isSome
  }
  let pres ← computeLCtxDiscrTrees choice fvarId?
  Core.checkSystem "infoview_search"
  for cand in ← getCandidates rootExpr subExpr gpos rwKind pres do
    sections := sections.push (← cand.generateSuggestions .hypothesis)

  let pres ← computeModuleDiscrTrees choice parentDecl?
  Core.checkSystem "infoview_search"
  for cand in ← getCandidates rootExpr subExpr gpos rwKind pres do
    sections := sections.push (← cand.generateSuggestions .fromFile)

  Core.checkSystem "infoview_search"
  let importTask? := some <| ← EIO.asTask <| ← dropM do
    computeImportDiscrTrees choice
    let cands ← getImportCandidates rootExpr subExpr gpos rwKind
    cands.mapM (·.generateSuggestions .fromImport)

  return { sections, importTask?, header :=
    <span> Lemma suggestions for {← exprToHtml subExpr}: </span> }

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
  let sections ← state.sections.mapM fun
    | .rw s => .rw <$> s.update (·.isDuplicate ·)
    | .grw s => .grw <$> s.update (·.isDuplicate ·)
    | .app s => .app <$> s.update (·.isDuplicate ·)
    | .appAt s => .appAt <$> s.update (·.isDuplicate ·)
  return { state with sections }

public def WidgetState.render (state : WidgetState)
    (subExpr : Html) : Html :=
  <FilterDetails
    summary={state.header}
    all={go false state subExpr}
    filtered={go true state subExpr}
    initiallyFiltered={true} />
where
  /-- Render all of the sections of lemma suggestions -/
  go (filter : Bool) (state : WidgetState)
      (subExpr : Html) : Html :=
    let htmls := state.sections.filterMap fun
      | .rw s => s.render filter "rw"
      | .grw s => s.render filter "grw"
      | .app s => s.render filter "apply"
      | .appAt s => s.render filter "apply at"
    let htmls := if state.importTask?.isNone then htmls else
      htmls.push <| .text "Imported theorems are being loaded..."
    if htmls.isEmpty then
      <p> No lemma suggestions found for {subExpr} </p>
    else
      .element "div" #[("style", json% {"marginLeft" : "4px"})] htmls

/-- Repeatedly run `updateWidgetState` until there is an update, and then return the result. -/
public partial def WidgetState.repeatRefresh (state : WidgetState)
    (subExpr : Html) (token : RefreshToken) : InfoviewSearchM Unit := do
  -- If there is nothing to compute, return the final (empty) display
  token.refresh (state.render subExpr)
  let mut state := state
  while !state.sections.all (·.isFinished) || state.importTask?.isSome do
    Core.checkSystem "infoview_search"
    -- Wait until some task has finished
    while !(← liftM <| state.sections.anyM (·.hasProgressed) <||> match state.importTask? with
        | none => pure false | some importTask => IO.hasFinished importTask) do
      IO.sleep 10
      Core.checkSystem "infoview_search"
    state ← updateWidgetState state
    token.refresh (state.render subExpr)
  markProgress -- TODO: remove this after refactoring

end InfoviewSearch
