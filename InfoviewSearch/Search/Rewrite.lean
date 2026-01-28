/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
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

namespace InfoviewSearch.Rw

open Lean Meta

/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
structure RewriteLemma where
  /-- The lemma -/
  name : Premise
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool

structure ResultId where
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

/-- A rewrite lemma that has been applied to an expression. -/
structure Rewrite extends RewriteLemma where
  /-- The proof of the rewrite -/
  proof : Expr
  /-- The replacement expression obtained from the rewrite -/
  replacement : Expr
  /-- The extra goals created by the rewrite -/
  extraGoals : Array (MVarId × BinderInfo)
  /-- Whether the rewrite introduces a new metavariable in the replacement expression -/
  makesNewMVars : Bool
  /-- Whether the rewrite is reflexive -/
  isRefl : Bool
  info : ResultId
  justLemmaName : Bool
  hyp? : Option Name
  occ : LOption Nat

set_option linter.style.emptyLine false in
/-- If `thm` can be used to rewrite `e`, return the rewrite. -/
def checkRewrite (lem : RewriteLemma) (rootExpr : Expr) (subExpr : SubExpr)
    (hyp? : Option Name) (occ : LOption Nat) : MetaM Rewrite := do
  let e := subExpr.expr
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
  let mut occ := occ
  for mvar in mvars, bi in binderInfos do
    unless ← mvar.mvarId!.isAssigned do
      if ← pure (!occ matches .undef) <&&> isProof mvar <&&> mvar.mvarId!.assumptionCore then
        justLemmaName := false
      else
        extraGoals := extraGoals.push (mvar.mvarId!, bi)

  let replacement ← instantiateMVars rhs
  let makesNewMVars ←
    pure (replacement.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome <||>
    extraGoals.anyM fun goal ↦ do
      let type ← instantiateMVars <| ← goal.1.getType
      return (type.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome
  let proof ← instantiateMVars proof
  let isRefl ← isExplicitEq e replacement
  if !occ matches .undef && justLemmaName then
    if ← withMCtx mctxOrig do kabstractFindsPositions rootExpr lhsOrig subExpr.pos then
      occ := .none
    else
      justLemmaName := false
  let info := {
    numGoals := extraGoals.size
    symm := lem.symm
    nameLenght := lem.name.length
    replacementSize := (← ppExpr replacement).pretty.length
    name := lem.name.toString
    replacement := ← abstractMVars replacement
  }
  return { lem with
    proof, replacement, extraGoals, makesNewMVars, isRefl, info, justLemmaName, occ, hyp? }

instance : Ord ResultId where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4).then <|
    (compare a.5 b.5)

def ResultId.isDuplicate (a b : ResultId) : MetaM Bool :=
  pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

open Widget ProofWidgets Jsx Server

/-- Return the rewrite tactic that performs the rewrite. -/
def tacticSyntax (rw : Rewrite) : MetaM (TSyntax `tactic) := do
  let proof ← if rw.justLemmaName then
      `(term| $(mkIdent <| ← rw.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab rw.proof)
  mkRewrite rw.occ rw.symm proof rw.hyp?

/-- Construct the `Result` from a `Rewrite`. -/
def Rewrite.toResult (rw : Rewrite) (pasteInfo : PasteInfo) : MetaM (Result ResultId) := do
  let tactic ← tacticSyntax rw
  let replacementString ← ppExprTagged rw.replacement
  let mut extraGoals := #[]
  for (mvarId, bi) in rw.extraGoals do
    -- TODO: think more carefully about which goals should be displayed
    -- Are there lemmas where a hypothesis is marked as implicit,
    -- which we would still want to show as a new goal?
    if bi.isExplicit then
      extraGoals := extraGoals.push (← ppExprTagged (← mvarId.getType))
  let mut htmls := #[<InteractiveCode fmt={replacementString}/>]
  for extraGoal in extraGoals do
    htmls := htmls.push
      <div> <strong className="goal-vdash">⊢ </strong> <InteractiveCode fmt={extraGoal}/> </div>
  let filtered ←
    if !rw.isRefl && !rw.makesNewMVars then
      some <$> mkSuggestion tactic pasteInfo (.element "div" #[] htmls)
    else
      pure none
  htmls := htmls.push (← rw.name.toHtml)
  let unfiltered ← mkSuggestion tactic pasteInfo (.element "div" #[] htmls)
  let pattern ← forallTelescopeReducing (← rw.name.getType) fun _ e => do
    let mkApp2 _ lhs rhs ← whnf e | throwError "Expected equation, not{indentExpr e}"
    ppExprTagged <| if rw.symm then rhs else lhs
  return { filtered, unfiltered, info := rw.info, pattern }

/-- `generateSuggestion` is called in parallel for all rewrite lemmas. -/
def generateSuggestion (rootExpr : Expr) (subExpr : SubExpr) (pasteInfo : PasteInfo)
    (hyp? : Option Name) (occ : LOption Nat) (lem : RewriteLemma) :
    MetaM (Result ResultId) := do
  withReducible do withNewMCtxDepth do
  let rewrite ← checkRewrite lem rootExpr subExpr hyp? occ
  rewrite.toResult pasteInfo

end InfoviewSearch.Rw
