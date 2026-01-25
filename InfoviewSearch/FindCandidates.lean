module

public import InfoviewSearch.Rewrite
public import InfoviewSearch.GRewrite
public import InfoviewSearch.Apply
public import InfoviewSearch.ApplyAt
public meta import InfoviewSearch.Initialize

/-!
# Discrimination tree lookup

This file defines how to build and match with the discrimination trees, for premises that are
- imported
- from the current module
- local hypotheses

## Performance note

When importing all of mathlib, building all of the discrimination trees takes on the order of 10-15
seconds. This is because of two distinct performance bottlenecks:

1. Looping through the environment, and computing all of the discrimination tree entries is
  expensive, and is done in parallel to speed it up.
2. Building the final discrimination tree by inserting all of the computed entries is les
  expensive, but it cannot be done in parallel, because a single datastructure is being built.

These two bottlenecks take up about the same amount oftime, but luckily,
we can already start doing (2) as soon as some of the parallel tasks from (1) have finished.
So, we build the discrimination tree (on the main thread) at the same time that the entries are
being computed on various parallel threads.
-/

meta section

namespace InfoviewSearch
open Lean Meta RefinedDiscrTree Rw Grw Apply ApplyAt

-- structure

/-- Return `true` if `s` and `t` are equal up to swapping the `MVarId`s. -/
def isMVarSwap (t s : Expr) : Bool :=
  go t s {} |>.isSome
where
  /-- The main loop of `isMVarSwap`. Returning `none` corresponds to a failure. -/
  go (t s : Expr) (swaps : List (MVarId × MVarId)) : Option (List (MVarId × MVarId)) := do
  let isTricky e := e.hasExprMVar || e.hasLevelParam
  if isTricky t then
    guard (isTricky s)
    match t, s with
    -- Note we don't bother keeping track of universe level metavariables.
    | .const n₁ _       , .const n₂ _        => guard (n₁ == n₂); some swaps
    | .sort _           , .sort _            => some swaps
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => go d₁ d₂ swaps >>= go b₁ b₂
    | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _     => go d₁ d₂ swaps >>= go b₁ b₂
    | .mdata d₁ e₁      , .mdata d₂ e₂       => guard (d₁ == d₂); go e₁ e₂ swaps
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => go t₁ t₂ swaps >>= go v₁ v₂ >>= go b₁ b₂
    | .app f₁ a₁        , .app f₂ a₂         => go f₁ f₂ swaps >>= go a₁ a₂
    | .proj n₁ i₁ e₁    , .proj n₂ i₂ e₂     => guard (n₁ == n₂ && i₁ == i₂); go e₁ e₂ swaps
    | .fvar fvarId₁     , .fvar fvarId₂      => guard (fvarId₁ == fvarId₂); some swaps
    | .lit v₁           , .lit v₂            => guard (v₁ == v₂); some swaps
    | .bvar i₁          , .bvar i₂           => guard (i₁ == i₂); some swaps
    | .mvar mvarId₁     , .mvar mvarId₂      =>
      match swaps.find? (·.1 == mvarId₁) with
      | none =>
        guard (swaps.all (·.2 != mvarId₂))
        let swaps := (mvarId₁, mvarId₂) :: swaps
        if mvarId₁ == mvarId₂ then
          some swaps
        else
          some <| (mvarId₂, mvarId₁) :: swaps
      | some (_, mvarId) => guard (mvarId == mvarId₂); some swaps
    | _                 , _                  => none
  else
    guard (t == s); some swaps


structure Entries where
  rw : Array (Key × LazyEntry × RewriteLemma) := #[]
  grw : Array (Key × LazyEntry × GRewriteLemma) := #[]
  app : Array (Key × LazyEntry × ApplyLemma) := #[]
  appAt : Array (Key × LazyEntry × ApplyAtLemma) := #[]

def insertEntry {α} (arr : Array (Key × LazyEntry × α)) (key : Expr) (a : α) :
    MetaM (Array (Key × LazyEntry × α)) := do
  return (← initializeLazyEntryWithEta key).foldl (init := arr) fun arr (key, lazy) ↦
    arr.push (key, lazy, a)

-- TODO: make `isBadMatch` more flexible, allowing the general equalities,
-- so that these lemmas are also in the discrimination tree.
-- We can then decide when/whether to actually show these lemmas.
/-- Determine whether the match `e` is too generic to be useful for insertion in
a discrimination tree of all imported theorems. -/
def isBadMatch (e : Expr) : Bool :=
  e.getAppFn.isMVar ||
  -- This extra check excludes lemmas that match a general equality
  -- these are almost never useful, and there are very many of them.
  e.eq?.any fun (α, l, r) =>
    α.getAppFn.isMVar && l.getAppFn.isMVar && r.getAppFn.isMVar && l != r

/-- Given a constant, compute what needs to be added to the various discrimination trees. -/
def Entries.addConst (entries : Entries) (name : Name) (cinfo : ConstantInfo) :
    MetaM Entries := do
  setMCtx {}
  let (xs, _, e) ← forallMetaTelescope cinfo.type
  let mut { rw, grw, app, appAt } := entries
  -- apply
  if !isBadMatch e then
    app ← insertEntry app e ⟨.const name⟩
  -- apply at
  if let some x := xs.back? then
    let e ← inferType x
    if !isBadMatch e then
      appAt ← insertEntry appAt e ⟨.const name⟩
  if let .app (.app rel lhs) rhs := e then
    let .const relName _ := rel.getAppFn | pure ()
    -- rw
    if relName matches ``Iff | ``Eq then
      if !isBadMatch lhs then
        rw ← insertEntry rw lhs ⟨.const name, false⟩
      if !isBadMatch rhs && (isBadMatch lhs || !isMVarSwap lhs rhs) then
        rw ← insertEntry rw rhs ⟨.const name, true⟩
    -- grw
    else
      if !isBadMatch lhs then
        grw ← insertEntry grw lhs ⟨.const name, false, relName⟩
      if !isBadMatch rhs then
        grw ← insertEntry grw rhs ⟨.const name, true, relName⟩
  return { rw, grw, app, appAt }

/-- Given a free variable, compute what needs to be added to the various discrimination trees. -/
def Entries.addVar (entries : Entries) (decl : LocalDecl) : MetaM Entries := do
  let (xs, _, e) ← forallMetaTelescope decl.type
  let mut { rw, grw, app, appAt } := entries
  -- apply
  app ← insertEntry app e ⟨.fvar decl.fvarId⟩
  -- apply at
  if let some x := xs.back? then
    let e ← inferType x
    appAt ← insertEntry appAt e ⟨.fvar decl.fvarId⟩
  if let .app (.app rel lhs) rhs := e then
    let .const relName _ := rel.getAppFn | pure ()
    -- rw
    if relName matches ``Iff | ``Eq then
      rw ← insertEntry rw lhs ⟨.fvar decl.fvarId, false⟩
      if !isMVarSwap lhs rhs then
        rw ← insertEntry rw rhs ⟨.fvar decl.fvarId, true⟩
    -- grw
    else
      grw ← insertEntry grw lhs ⟨.fvar decl.fvarId, false, relName⟩
      grw ← insertEntry grw rhs ⟨.fvar decl.fvarId, true, relName⟩
  return { rw, grw, app, appAt }

public structure PreDiscrTrees where
  rw : PreDiscrTree RewriteLemma    := {}
  grw : PreDiscrTree GRewriteLemma  := {}
  app : PreDiscrTree ApplyLemma     := {}
  appAt : PreDiscrTree ApplyAtLemma := {}

def PreDiscrTrees.append (pres : PreDiscrTrees) (maps : Entries) : PreDiscrTrees where
  rw := maps.rw.foldl (init := pres.rw) fun pre (key, e) ↦ pre.push key e
  grw := maps.grw.foldl (init := pres.grw) fun pre (key, e) ↦ pre.push key e
  app := maps.app.foldl (init := pres.app) fun pre (key, e) ↦ pre.push key e
  appAt := maps.appAt.foldl (init := pres.appAt) fun pre (key, e) ↦ pre.push key e

public initialize rwRef : IO.Ref (Option (RefinedDiscrTree RewriteLemma)) ← IO.mkRef none
public initialize grwRef : IO.Ref (Option (RefinedDiscrTree GRewriteLemma)) ← IO.mkRef none
public initialize appRef : IO.Ref (Option (RefinedDiscrTree ApplyLemma)) ← IO.mkRef none
public initialize appAtRef : IO.Ref (Option (RefinedDiscrTree ApplyAtLemma)) ← IO.mkRef none

public def computeImportDiscrTrees : CoreM Unit := do
  let (tasks, errors) ← foldEnv {} Entries.addConst 5000
  let pre : PreDiscrTrees := tasks.foldl (·.append ·.get) {}
  rwRef.set pre.rw.toRefinedDiscrTree
  grwRef.set pre.grw.toRefinedDiscrTree
  appRef.set pre.app.toRefinedDiscrTree
  appAtRef.set pre.appAt.toRefinedDiscrTree
  --TODO: Maybe we should rather panic, because the logging messages will be discarded...
  logImportFailures errors

public def computeModuleDiscrTrees (parentDecl? : Option Name) : CoreM PreDiscrTrees := do
  let (pre, errors) ← foldCurrModule {} fun entries name cinfo ↦
    if name == parentDecl? then pure entries else entries.addConst name cinfo
  logImportFailures errors
  return .append {} pre

public def computeLCtxDiscrTrees (fvarId? : Option FVarId) : MetaM PreDiscrTrees := withReducible do
  let mut entries : Entries := {}
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && fvarId?.all (· != decl.fvarId) then
      entries ← entries.addVar decl
  return .append {} entries


public def getImportMatches {α} (ref : IO.Ref (Option (RefinedDiscrTree α))) (e : Expr) :
    MetaM (MatchResult α) := do
  let some tree ← ref.swap none |
    -- TODO: implement this thing via a task/promise. Then if it is none, we panic! here.
    computeImportDiscrTrees; getImportMatches ref e
  let (candidates, tree) ← getMatch tree e false false
  ref.set (some tree)
  MonadExcept.ofExcept candidates

public def getMatches {α} (tree : RefinedDiscrTree α) (e : Expr) : MetaM (MatchResult α) := do
  let (candidates, _) ← getMatch tree e false false
  MonadExcept.ofExcept candidates

end InfoviewSearch
