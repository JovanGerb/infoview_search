/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Util
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Push

/-!
# Suggestions for normalization tactics
-/

meta section

namespace InfoviewSearch

open Lean Meta ProofWidgets Jsx Mathlib.Tactic Mathlib.Meta

public structure RewritingInfo where
  hyp? : Option Name
  convPath? : Option Conv.Path

/--
Given that a normalization tactic changed `old` to `new`, return the suggestion for this tactic.
Note that some tactics have no `conv` analogue, so in that case we
default to suggesting the usual version of the tactic.
-/
def suggestNormalize (old new : Expr) (info : RewritingInfo)
    (tacStx : Option Ident → CoreM (TSyntax `tactic))
    (convStx : OptionT CoreM (TSyntax `conv) := failure) : InfoviewSearchM (Option Html) := do
  if ← isExplicitEq old new then return none
  let tac ← match ← convStx.run, info.convPath? with
    | some convStx, some path =>
      Conv.pathToStx convStx path info.hyp?
    | _, _ =>
      tacStx (info.hyp?.map mkIdent)
  mkTacticSuggestion tac (← tacStx none) (← exprToHtml new)

section Cast

def normCastStx (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| norm_cast $[at $hyp?:ident]?)

def pushCastStx (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| push_cast $[at $hyp?:ident]?)

def runNormCast (e : Expr) : MetaM Expr := do
  return (← Lean.Elab.Tactic.NormCast.derive e).1

def runPushCast (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← NormCast.pushCastExt.getTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Lean.Meta.simp e ctx).1.expr

/-- Create a suggestion for `norm_cast` and/or `push_cast`. -/
public def suggestNormCast (e : Expr) (info : RewritingInfo) : InfoviewSearchM Html :=
  mkIncrementalSuggestions "cast" fun update ↦ do
    let e' ← runNormCast e
    if let some html ← suggestNormalize e e' info normCastStx `(conv| norm_cast) then
      update html
    let e' ← runPushCast e
    -- Note: there is no `conv` version of `push_cast`.
    if let some html ← suggestNormalize e e' info pushCastStx then
      update html

end Cast

section Push

def pushNegStx (distrib : Bool) (hyp? : Option Ident) : CoreM (TSyntax `tactic) := do
  let cfg ←
    if distrib then `(Parser.Tactic.optConfig| +$(mkIdent `distrib))
    else `(Parser.Tactic.optConfig| )
  `(tactic| push_neg $cfg $[at $hyp?:ident]?)

def pushNegConvStx (distrib : Bool) : CoreM (TSyntax `conv) := do
  let cfg ←
    if distrib then `(Parser.Tactic.optConfig| +$(mkIdent `distrib))
    else `(Parser.Tactic.optConfig| )
  `(conv| push_neg $cfg)

def pushStx (head : Push.Head) (hyp? : Option Ident) : CoreM (TSyntax `tactic) := do
  let head ← match head with
    | .lambda => `(fun _ ↦ _)
    | .forall => `(∀ _, _)
    | .const ``Membership.mem => `(_ ∈ _)
    | .const c => `($(mkIdent (← unresolveNameGlobal c)):ident)
  `(tactic| push $head:term $[at $hyp?:ident]?)

def pushConvStx (head : Push.Head) : CoreM (TSyntax `conv) := do
  let head ← match head with
    | .lambda => `(fun _ ↦ _)
    | .forall => `(∀ _, _)
    | .const ``Membership.mem => `(_ ∈ _)
    | .const c => `($(mkIdent (← unresolveNameGlobal c)):ident)
  `(conv| push $head:term)

def runPush (head : Push.Head) (distrib : Bool) (e : Expr) : MetaM Expr := do
  return (← Push.pushCore head { distrib } none e).expr

def getHead (e : Expr) : Option Push.Head :=
  match e.getAppFn with
  | .forallE .. => some .forall
  | .lam .. => some .lambda
  | .const c _ => some (.const c)
  | _ => none

/-- Create a suggestion for `push` or `push_neg`. -/
public def suggestPush (e : Expr) (info : RewritingInfo) : InfoviewSearchM Html := do
  let some head := getHead (← whnfR e) | return .text ""
  let thms := Push.pushExt.getState (← getEnv)
  if let .const headConst := head then
    -- Make sure that there are actually push theorems for this constant, otherwise return.
    try
      thms.root.forM fun | .const c _, _ => do if c == headConst then failure | _, _ => pure ()
      return .text ""
    catch _ => pure ()
  mkIncrementalSuggestions "push" fun update ↦ do
    let e₁ ← runPush head false e
    if head matches .const ``Not then
      if let some html ← suggestNormalize e e₁ info (pushNegStx false) (pushNegConvStx false) then
        update html
      let e₂ ← runPush head true e
      if let some html ← suggestNormalize e₁ e₂ info (pushNegStx true) (pushNegConvStx true) then
        update html
    else
      if let some html ← suggestNormalize e e₁ info (pushStx head) (pushConvStx head) then
        update html

end Push

section Simp

def dsimpOnlyStx (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| dsimp only $[at $hyp?:ident]?)

def dsimpStx (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| dsimp $[at $hyp?:ident]?)

def simpStx (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| simp $[at $hyp?:ident]?)

def normNumStx (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| norm_num $[at $hyp?:ident]?)

def runDSimpOnly (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Lean.Meta.dsimp e ctx).1

def runDSimp (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Lean.Meta.dsimp e ctx).1

def runSimp (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Lean.Meta.simp e ctx).1.expr

def runNormNum (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← NormNum.deriveSimp ctx e (useSimp := true)).expr

/--
Create suggestions for `dsimp only`, `dsimp`, `simp`, `norm_num`.
We only suggest a tactic if it gives a different result compared to the previous result.

TODO: is it really preferred to suggest `dsimp` over `simp` when both do the same.
And what about `dsimp only` and `dsimp`?

TODO: if the simplification closes the goal, then let the user know about this explicitly,
instead of simplifying to `True`.
-/
public def suggestSimp (e : Expr) (info : RewritingInfo) : InfoviewSearchM Html :=
  mkIncrementalSuggestions "simp" fun update ↦ do
    let e₁ ← runDSimpOnly e
    if let some html ← suggestNormalize e e₁ info dsimpOnlyStx `(conv| dsimp only) then
      update html
    let e₂ ← runDSimp e
    if let some html ← suggestNormalize e₁ e₂ info dsimpStx `(conv| dsimp) then
      update html
    let e₃ ← runSimp e
    if let some html ← suggestNormalize e₂ e₃ info simpStx `(conv| simp) then
      update html
    let e₄ ← runNormNum e
    if let some html ← suggestNormalize e₃ e₄ info normNumStx `(conv| norm_num) then
      update html

end Simp

section Algebra

def ringNFStx (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| ring_nf $[at $hyp?:ident]?)

def abelNFStx (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| abel_nf $[at $hyp?:ident]?)

def fieldSimpStx (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| field_simp $[at $hyp?:ident]?)

def groupStx (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| group $[at $hyp?:ident]?)

def noncommRingSyntax (_hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| noncomm_ring) -- `noncomm_ring` doesn't even support the `at h` syntax???

open RingNF in
def runRing (e : Expr) (isProp : Bool) : MetaM Expr :=
  (fun expr ↦ return (← cleanup {} { expr }).expr) =<< AtomM.run .reducible do
    if isProp then
      let mkApp2 rel lhs rhs := e | failure
      return mkApp2 rel (← evalExpr lhs).expr (← evalExpr rhs).expr
    else
      return (← evalExpr e).expr

open Abel in
def runAbel (e : Expr) (isProp : Bool) : MetaM Expr :=
  (fun expr ↦ return (← cleanup {} { expr }).expr) =<< AtomM.run .reducible do
    if isProp then
      let mkApp2 rel lhs rhs := e | failure
      return mkApp2 rel (← evalExpr lhs).expr (← evalExpr rhs).expr
    else
      return (← evalExpr e).expr

def runField (e : Expr) (isProp : Bool) : MetaM Expr := AtomM.run .reducible do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let disch := fun e ↦ Prod.fst <$> (FieldSimp.discharge e).run ctx >>= Option.getM
  if isProp then
    return (← FieldSimp.reduceProp disch e).expr
  else
    return (← FieldSimp.reduceExpr disch e).expr

def runGroup (e : Expr) (isProp : Bool) : MetaM Expr := do
  unless isProp do failure -- There's no easy way to run `group` on an expression
  let mvar ← mkFreshExprMVar e
  _ ← Elab.runTactic mvar.mvarId! (← `(tactic| group))
  instantiateMVars (← inferType mvar)

def runNoncommRing (e : Expr) (isProp : Bool) : MetaM Expr := do
  unless isProp do failure -- There's no easy way to run `noncomm_ring` on an expression
  let mvar ← mkFreshExprMVar e
  _ ← Elab.runTactic mvar.mvarId! (← `(tactic| noncomm_ring))
  instantiateMVars (← inferType mvar)

/-- Check if `e` is a target for algebraic simplification. -/
def isAlgebraic (e : Expr) : MetaM (Option (Bool × Expr)) := do
  if (← whnfR e).getAppFn.constName matches
    ``HAdd.hAdd | ``Add.add |
    ``HMul.hMul | ``Mul.mul |
    ``HSMul.hSMul | ``SMul.smul |
    ``HPow.hPow | ``Pow.pow |
    ``Neg.neg |
    ``HSub.hSub | ``Sub.sub |
    ``Inv.inv |
    ``HDiv.hDiv | ``Div.div then
    return (false, ← inferType e)
  else
    let (_, α, _, _) ← try e.ineq? catch _ => return none
    return (true, α)
/--
Create a suggestion for an algebraic normalization tactic.

We suggest `field_simp` when applicable, and additionally we suggest at most one of
`ring`, `noncomm_ring`, `abel` and `group`.

There are 2 cases where we may suggest this
1. The selected expression is an algebraic expression.
2. The selected expression is an equality or inequality of algebraic expressions.
-/
public def suggestAlgebraicNormalization (e : Expr) (info : RewritingInfo) :
    InfoviewSearchM Html := do
  let some (isProp, type) ← isAlgebraic e | return .text ""
  mkIncrementalSuggestions "algebra" fun update ↦ do
    if let some e' ← try? <| runField e isProp then
      if let some html ← suggestNormalize e e' info fieldSimpStx `(conv| field_simp) then
        update html
    if let some e' ← try? <| runRing e isProp then
      if let some html ← suggestNormalize e e' info ringNFStx `(conv| ring_nf) then
        update html
    else if let .some _ ← trySynthInstance (← mkAppM ``NonAssocSemiring #[type]) then
      if let some e' ← try? <| runNoncommRing e isProp then
        if let some html ← suggestNormalize e e' info noncommRingSyntax then
          update html
    else if let some e' ← try? <| runAbel e isProp then
      if let some html ← suggestNormalize e e' info abelNFStx `(conv| abel_nf) then
        update html
    else if let .some _ ← trySynthInstance (← mkAppM ``Group #[type]) then
      if let some e' ← try? <| runGroup e isProp then
        if let some html ← suggestNormalize e e' info groupStx then
          update html

end Algebra

end InfoviewSearch
