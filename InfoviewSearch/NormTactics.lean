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

structure NormStx where
  tac : Option Ident → CoreM (TSyntax `tactic)
  conv : OptionT CoreM (TSyntax `conv)

/--
Given that a normalization tactic changed `old` to `new`, return the suggestion for this tactic.
Note that some tactics have no `conv` analogue, so in that case we
default to suggesting the usual version of the tactic.
-/
def suggestNormalize (old new : Expr) (info : RewritingInfo) (stx : NormStx) :
    InfoviewSearchM (Option Html) := do
  if ← isExplicitEq old new then return none
  let tac ← match ← stx.conv.run, info.convPath? with
    | some convStx, some path =>
      Conv.pathToStx convStx path info.hyp?
    | _, _ =>
      stx.tac (info.hyp?.map mkIdent)
  let mut html ← exprToHtml new
  if new.isTrue then
    -- TODO: decide whether to put a `🎉` emoji depending on the logical position of the expression
    -- In fact, we could even have a negative emoji if the step turns out to be useless,
    -- e.g. when turning the goal into `False`, or a hypothesis into `True`.
    html := <span> {html} {.text " 🎉"} </span>
  mkTacticSuggestion tac (← stx.tac none) html

section Cast

def normCastStx : NormStx where
  tac hyp? := `(tactic| norm_cast $[at $hyp?:ident]?)
  conv     := `(conv| norm_cast)

def pushCastStx : NormStx where
  tac hyp? := `(tactic| push_cast $[at $hyp?:ident]?)
  conv     := failure

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
    if let some html ← suggestNormalize e e' info normCastStx then
      update html
    let e' ← runPushCast e
    -- Note: there is no `conv` version of `push_cast`.
    if let some html ← suggestNormalize e e' info pushCastStx then
      update html

end Cast

section Push

def pushNegStx (distrib : Bool) : NormStx :=
  let cfg := do
    if distrib then `(Parser.Tactic.optConfig| +$(mkIdent `distrib))
    else `(Parser.Tactic.optConfig| )
  {
    tac hyp? := do `(tactic| push_neg $(← cfg) $[at $hyp?:ident]?)
    conv     := do `(conv| push_neg $(← cfg))
  }

def pushStx (head : Push.Head) : NormStx :=
  let head := do
    match head with
    | .lambda => `(fun _ ↦ _)
    | .forall => `(∀ _, _)
    | .const ``Membership.mem => `(_ ∈ _)
    | .const c => `($(mkIdent (← unresolveNameGlobal c)):ident)
  {
    tac hyp? := do `(tactic| push $(← head):term $[at $hyp?:ident]?)
    conv     := do `(conv| push $(← head):term)
  }

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
      if let some html ← suggestNormalize e e₁ info (pushNegStx false) then
        update html
      let e₂ ← runPush head true e
      if let some html ← suggestNormalize e₁ e₂ info (pushNegStx true) then
        update html
    else
      if let some html ← suggestNormalize e e₁ info (pushStx head) then
        update html

end Push

section Simp

def dsimpOnlyStx : NormStx where
  tac hyp? := `(tactic| dsimp only $[at $hyp?:ident]?)
  conv     := `(conv| dsimp only)

def dsimpStx : NormStx where
  tac hyp? := `(tactic| dsimp $[at $hyp?:ident]?)
  conv     := `(conv| dsimp)

def simpStx : NormStx where
  tac hyp? := `(tactic| simp $[at $hyp?:ident]?)
  conv     := `(conv| simp)

def normNumStx : NormStx where
  tac hyp? := `(tactic| norm_num $[at $hyp?:ident]?)
  conv     := `(conv| norm_num)

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
-/
public def suggestSimp (e : Expr) (info : RewritingInfo) : InfoviewSearchM Html :=
  mkIncrementalSuggestions "simp" fun update ↦ do
    let e₁ ← runDSimpOnly e
    if let some html ← suggestNormalize e e₁ info dsimpOnlyStx then
      update html
    let e₂ ← runDSimp e
    if let some html ← suggestNormalize e₁ e₂ info dsimpStx then
      update html
    let e₃ ← runSimp e
    if let some html ← suggestNormalize e₂ e₃ info simpStx then
      update html
    let e₄ ← runNormNum e
    if let some html ← suggestNormalize e₃ e₄ info normNumStx then
      update html

end Simp

section Algebra

def ringNFStx : NormStx where
  tac hyp? := `(tactic| ring_nf $[at $hyp?:ident]?)
  conv     := `(conv| ring_nf)

def abelNFStx : NormStx where
  tac hyp? := `(tactic| abel_nf $[at $hyp?:ident]?)
  conv     := `(conv| abel_nf)

def fieldSimpStx : NormStx where
  tac hyp? := `(tactic| field_simp $[at $hyp?:ident]?)
  conv     := `(conv| field_simp)

-- `group` doesn't have a `conv` version.
def groupStx : NormStx where
  tac hyp? := `(tactic| group $[at $hyp?:ident]?)
  conv     := failure

 -- `noncomm_ring` doesn't even have an `at h` version.
def noncommRingStx : NormStx where
  tac _ := `(tactic| noncomm_ring)
  conv     := failure

open RingNF in
def runRing (e : Expr) (ineq? : Option Mathlib.Ineq) : MetaM Expr :=
  (fun expr ↦ return (← cleanup {} { expr }).expr) =<< AtomM.run .reducible do
    if let some ineq := ineq? then
      let mkApp2 rel lhs rhs := e | failure
      let lhs := (← evalExpr lhs).expr; let rhs := (← evalExpr rhs).expr
      if ← isDefEq lhs rhs then
        match ineq with
        | .eq | .le => return mkConst ``True
        | .lt => return mkConst ``False
      return mkApp2 rel lhs rhs
    else
      return (← evalExpr e).expr

open Abel in
def runAbel (e : Expr) (ineq? : Option Mathlib.Ineq) : MetaM Expr :=
  (fun expr ↦ return (← cleanup {} { expr }).expr) =<< AtomM.run .reducible do
    if let some ineq := ineq? then
      let mkApp2 rel lhs rhs := e | failure
      let lhs := (← evalExpr lhs).expr; let rhs := (← evalExpr rhs).expr
      if ← isDefEq lhs rhs then
        match ineq with
        | .eq | .le => return mkConst ``True
        | .lt => return mkConst ``False
      return mkApp2 rel lhs rhs
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

private def tryTactic (stx : TSyntax `tactic) (e : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprMVar e
  match ← (Elab.Tactic.run mvar.mvarId! (Elab.Tactic.evalTactic stx)).run' with
  | [] => return mkConst ``True
  | [mvarId] => mvarId.getType
  | _ => failure

def runGroup (e : Expr) : MetaM Expr := do
  tryTactic (← `(tactic| group)) e

def runNoncommRing (e : Expr) : MetaM Expr := do
  tryTactic (← `(tactic| noncomm_ring)) e

/-- Check if `e` is a target for algebraic simplification. -/
def isAlgebraic (e : Expr) : MetaM (Option ((Option Mathlib.Ineq) × Expr)) := do
  if (← whnfR e).getAppFn.constName matches
    ``HAdd.hAdd | ``Add.add |
    ``HMul.hMul | ``Mul.mul |
    ``HSMul.hSMul | ``SMul.smul |
    ``HPow.hPow | ``Pow.pow |
    ``Neg.neg |
    ``HSub.hSub | ``Sub.sub |
    ``Inv.inv |
    ``HDiv.hDiv | ``Div.div then
    return some (none, ← inferType e)
  try
    let (kind, α, _, _) ← e.ineq?
    return some (some kind, α)
  catch _ =>
    return none

/--
Create a suggestion for an algebraic normalization tactic.

We suggest `field_simp` when applicable, and additionally we suggest at most one of
`ring`, `noncomm_ring`, `abel` and `group`, depending on which type class is satisfied.

There are 2 cases where we may suggest this
1. The selected expression is an algebraic expression.
2. The selected expression is an equality or inequality of algebraic expressions.
-/
public def suggestAlgebraicNormalization (e : Expr) (info : RewritingInfo) :
    InfoviewSearchM Html := do
  let some (ineq?, type) ← isAlgebraic e | return .text ""
  mkIncrementalSuggestions "algebra" fun update ↦ do
    if let some e' ← try? <| runField e ineq?.isSome then
      if let some html ← suggestNormalize e e' info fieldSimpStx then
        update html
    if let some e' ← try? <| runRing e ineq? then
      if let some html ← suggestNormalize e e' info ringNFStx then
        update html
    else if let .some _ ← trySynthInstance (← mkAppM ``NonAssocSemiring #[type]) then
      if ineq?.isSome then
        if let some e' ← try? <| runNoncommRing e then
          if let some html ← suggestNormalize e e' info noncommRingStx then
            update html
    else if let some e' ← try? <| runAbel e ineq? then
      if let some html ← suggestNormalize e e' info abelNFStx then
        update html
    else if let .some _ ← trySynthInstance (← mkAppM ``Group #[type]) then
      if ineq?.isSome then
        if let some e' ← try? <| runGroup e then
          if let some html ← suggestNormalize e e' info groupStx then
            update html

end Algebra

end InfoviewSearch
