/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Search.SectionState

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

public meta section

namespace InfoviewSearch

open Lean Meta Widget ProofWidgets Jsx Server

/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
structure RwLemma where
  /-- The lemma -/
  name : Premise
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool

structure RwInfo where
  pasteInfo : PasteInfo
  rootExpr : Expr
  subExpr : Expr
  pos : SubExpr.Pos
  hyp? : Option Name
  rwKind : RwKind

structure RwKey where
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

instance : Ord RwKey where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4).then <|
    (compare a.5 b.5)

def RwKey.isDuplicate (a b : RwKey) : MetaM Bool :=
  pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

/-- Return the rewrite tactic that performs the rewrite. -/
private def tacticSyntax (lem : RwLemma) (rwKind : RwKind) (hyp? : Option Name) (proof : Expr)
    (justLemmaName : Bool) : MetaM (TSyntax `tactic) := do
  let proof ← if justLemmaName then
      `(term| $(mkIdent <| ← lem.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
  mkRewrite rwKind lem.symm proof hyp?

set_option linter.style.emptyLine false in

def RwLemma.generateSuggestion (i : RwInfo) (lem : RwLemma) : MetaM (Result RwKey) :=
  withReducible do withNewMCtxDepth do
  let e := i.subExpr
  let (proof, mvars, binderInfos, eqn) ← lem.name.forallMetaTelescopeReducing
  let mkApp2 _ lhs rhs ← whnf eqn | throwError "Exected an equality or iff, not {eqn}"
  let (lhs, rhs) := if lem.symm then (rhs, lhs) else (lhs, rhs)
  let lhsOrig := lhs; let mctxOrig ← getMCtx
  unless ← isDefEq lhs e do throwError "{lhs} does not unify with {e}"
  -- just like in `kabstract`, we compare the `HeadIndex` and number of arguments
  let lhs ← instantiateMVars lhs
  -- TODO: if the `headIndex` doesn't match, then use `simp_rw` instead of `rw` in the suggestion,
  -- instead of just not showing the suggestion.
  if lhs.toHeadIndex != e.toHeadIndex || lhs.headNumArgs != e.headNumArgs then
    throwError "{lhs} and {e} do not match according to the head-constant indexing"
  synthAppInstances `infoview_search default mvars binderInfos false false
  let mut extraGoals := #[]
  let mut justLemmaName := true
  let mut rwKind := i.rwKind
  for mvar in mvars, bi in binderInfos do
    unless ← mvar.mvarId!.isAssigned do
      if ← pure (rwKind matches .valid ..) <&&> isProof mvar <&&> mvar.mvarId!.assumptionCore then
        justLemmaName := false
      else
        extraGoals := extraGoals.push (← instantiateMVars (← inferType mvar), bi)

  let replacement ← instantiateMVars rhs
  let makesNewMVars :=
    (replacement.findMVar? (mvars.contains <| .mvar ·)).isSome ||
    extraGoals.any fun goal ↦ (goal.1.findMVar? (mvars.contains <| .mvar ·)).isSome
  let proof ← instantiateMVars proof
  let isRefl ← isExplicitEq e replacement
  if let .valid tpCorrect _ := rwKind then
    if justLemmaName then
      if ← withMCtx mctxOrig do kabstractFindsPositions i.rootExpr lhsOrig i.pos then
        rwKind := .valid tpCorrect none
      else
        justLemmaName := false
  let key := {
    numGoals := extraGoals.size
    symm := lem.symm
    nameLenght := lem.name.length
    replacementSize := (← ppExpr replacement).pretty.length
    name := lem.name.toString
    replacement := ← abstractMVars replacement
  }
  let tactic ← tacticSyntax lem rwKind i.hyp? proof justLemmaName
  let mut explicitGoals := #[]
  for (mvarId, bi) in extraGoals do
    -- TODO: think more carefully about which goals should be displayed
    -- Are there lemmas where a hypothesis is marked as implicit,
    -- which we would still want to show as a new goal?
    if bi.isExplicit then
      explicitGoals := explicitGoals.push (← ppExprTagged mvarId)
  let mut htmls := #[<InteractiveCode fmt={← ppExprTagged replacement}/>]
  for extraGoal in explicitGoals do
    htmls := htmls.push
      <div> <strong className="goal-vdash">⊢ </strong> <InteractiveCode fmt={extraGoal}/> </div>
  let filtered ←
    if !isRefl && !makesNewMVars then
      some <$> mkSuggestion tactic i.pasteInfo (.element "div" #[] htmls)
    else
      pure none
  htmls := htmls.push (<div> {← lem.name.toHtml} </div>)
  let unfiltered ← mkSuggestion tactic i.pasteInfo (.element "div" #[] htmls)
  let pattern ← forallTelescopeReducing (← lem.name.getType) fun _ e => do
    let mkApp2 _ lhs rhs ← whnf e | throwError "Expected equation, not{indentExpr e}"
    ppExprTagged <| if lem.symm then rhs else lhs
  return { filtered, unfiltered, key, pattern }


end InfoviewSearch
