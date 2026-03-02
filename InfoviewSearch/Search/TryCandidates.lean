/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Search.FindCandidates
public meta import InfoviewSearch.RefreshComponent -- TODO: this should not need `meta`...

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
@[specialize]
def getCandidatesAux (rootExpr subExpr : Expr) (gpos : Array GrwPos) (rwKind : RwKind)
    (report : String → BaseIO Unit)
    (rw : Expr → MetaM (MatchResult RwLemma)) (grw : Expr → MetaM (MatchResult GrwLemma))
    (app : Expr → MetaM (MatchResult ApplyLemma)) (appAt : Expr → MetaM (MatchResult ApplyAtLemma))
    : InfoviewSearchM (Array Candidates) := do
  let mut cands : Std.TreeMap Nat (Array Candidates) := {}
  /- The order in which we show the suggestions for the same pattern for different tactics
  depends on the following insertion order.
  We choose the order `grw` => `rw` => `apply(at)`. -/
  if !gpos.isEmpty then
    report "grw"
    cands := cands ++ (← grw subExpr).elts.map fun _ ↦ (·.map <|
      .grw { rootExpr, subExpr, rwKind, gpos })
  report "rw"
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
      report "apply at"
      cands := cands ++ (← appAt rootExpr).elts.map fun _ ↦ (·.map .appAt)
    else
      report "apply"
      cands := cands ++ (← app rootExpr).elts.map fun _ ↦ (·.map .app)
  return cands.foldr (init := #[]) fun _ val acc ↦ acc ++ val

@[specialize]
def getImportCandidates (rootExpr subExpr : Expr) (gpos : Array GrwPos)
    (rwKind : RwKind) (report : String → BaseIO Unit) : InfoviewSearchM (Array Candidates) :=
  getCandidatesAux rootExpr subExpr gpos rwKind report
    (getImportMatches rwRef) (getImportMatches grwRef)
    (getImportMatches appRef) (getImportMatches appAtRef)

def getCandidates (rootExpr subExpr : Expr) (gpos : Array GrwPos)
    (rwKind : RwKind) (pres : PreDiscrTrees) : InfoviewSearchM (Array Candidates) :=
  getCandidatesAux rootExpr subExpr gpos rwKind (fun _ ↦ pure ())
    (getMatches pres.rw.toRefinedDiscrTree) (getMatches pres.grw.toRefinedDiscrTree)
    (getMatches pres.app.toRefinedDiscrTree) (getMatches pres.appAt.toRefinedDiscrTree)

/-- Run `f` on the results of all tasks in the array of tasks, in an arbitrary order.

TODO: use Lean's `Mutex` to avoid the polling loop? -/
@[specialize]
private partial def forTasksM {α} (tasks : Array (Task α)) (f : α → MetaM Unit) : MetaM Unit := do
  if tasks.isEmpty then return
  Core.checkInterrupted
  if ← ↑(tasks.anyM IO.hasFinished) then
    let tasks ← tasks.filterM fun task ↦ do
      let finished ← IO.hasFinished task
      if finished then
        f task.get
      return !finished
    forTasksM tasks f
  else
    IO.sleep 10
    forTasksM tasks f

/-- Spawn tasks for the given candidate premises and
return an HTML that shows the incoming results -/
def runSuggestions (kind : SectionKind) : Candidates → InfoviewSearchM Html
  | .rw info arr => go "rw" (·.isDuplicate ·) arr (·.name) (·.try info)
  | .grw info arr => go "grw" (·.isDuplicate ·) arr (·.name) (·.try info)
  | .app arr => go "apply" (·.isDuplicate ·) arr (·.name) (·.try)
  | .appAt arr => go "apply at" (·.isDuplicate ·) arr (·.name) (·.try)
where
  @[specialize]
  go {α β} [Ord α] [Inhabited α] (tactic : String) (isDup : α → α → MetaM Bool)
      (candidates : Array β) (premise : β → Premise)
      (mkSuggestion : β → InfoviewSearchM (Result α)) : InfoviewSearchM Html := do
    let (html, token) ← mkRefreshComponent {} (renderSection tactic kind)
    let tasks ← candidates.mapM fun lem ↦ spawnTask (premise lem) (mkSuggestion lem)
    discard <| BaseIO.asTask (prio := .dedicated) <| (← dropM <| trackingComputation tactic do
      forTasksM tasks fun
        | .ok (some res) => insertResult token res isDup
        | .ok none => pure ()
        | .error e => SectionToken.pushError token e).catchExceptions fun ex ↦ do
          if let .internal ex := ex then
            if ex == interruptExceptionId then
              return
          (panic! s!"Error when processing {tactic}: {← ex.toMessageData.toString}")
    return html

set_option linter.style.emptyLine false in
public def librarySearchSuggestions (rootExpr subExpr : Expr)
    (rwKind : RwKind) (parentDecl? : Option Name)
    (token : RefreshToken Html) : InfoviewSearchM Unit := do
  trackingComputation "discrimination tree search" do
  Core.checkInterrupted
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

  Core.checkInterrupted
  token.set <div> loading local hypotheses ⏳ </div>
  let pres ← computeLCtxDiscrTrees choice fvarId?
  Core.checkInterrupted
  for cand in ← getCandidates rootExpr subExpr gpos rwKind pres do
    sections := sections.push (← runSuggestions .hyp cand)

  Core.checkInterrupted
  token.set <div>
    {.element "div" #[] sections}
    <div> loading theorem in the current file ⏳ </div>
    </div>
  let pres ← computeModuleDiscrTrees choice parentDecl?
  Core.checkInterrupted
  for cand in ← getCandidates rootExpr subExpr gpos rwKind pres do
    sections := sections.push (← runSuggestions .currFile cand)

  Core.checkInterrupted
  token.set <div>
    {.element "div" #[] sections}
    <div> initializing discrimination trees ⏳ </div>
    </div>
  computeImportDiscrTrees choice
  Core.checkInterrupted
  -- TODO: more fine grained messages so that we can see if e.g. `rw` or `apply` is being loaded.
  let report (tac : String) :=
    token.set <div>
      {.element "div" #[] sections}
      <div> {.text s!"loading imported `{tac}` theorems ⏳"} </div>
      </div>
  for cand in ← getImportCandidates rootExpr subExpr gpos rwKind report do
    sections := sections.push (← runSuggestions .imported cand)

  token.set <div>
    {.element "div" #[] sections}
    </div>
  unless sections.isEmpty do
    markProgress

end InfoviewSearch
