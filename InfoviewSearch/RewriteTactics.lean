/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Util
public import InfoviewSearch.RefreshComponent
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.FieldSimp

meta section

namespace InfoviewSearch

open Lean Meta ProofWidgets Jsx Mathlib.Tactic Mathlib.Meta

public structure RewritingInfo where
  pasteInfo : PasteInfo
  hyp? : Option Name
  convPath? : Option Conv.Path

def renderRewritingTactic (old new : Expr)
    (info : RewritingInfo)
    (tacStx : Option Ident → CoreM (TSyntax `tactic))
    (convStx : CoreM (TSyntax `conv)) : MetaM (Option Html) := do
  if ← isExplicitEq old new then return none
  let replacement := <InteractiveCode fmt={← Widget.ppExprTagged new}/>
  -- TODO: also print the tactic name as part of the suggestion?
  let tac ← match info.convPath? with
    | some path => Conv.pathToStx (← convStx) path info.hyp?
    | none => tacStx (info.hyp?.map mkIdent)
  some <$> mkSingleSuggestion tac info.pasteInfo replacement

def normCastSyntax (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| norm_cast $[at $hyp?:ident]?)

def ringNFSyntax (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| ring_nf $[at $hyp?:ident]?)

def fieldSimpSyntax (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| field_simp $[at $hyp?:ident]?)

def dsimpOnlySyntax (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| dsimp only $[at $hyp?:ident]?)

def dsimpSyntax (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| dsimp $[at $hyp?:ident]?)

def simpSyntax (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| simp $[at $hyp?:ident]?)

def normNumSyntax (hyp? : Option Ident) : CoreM (TSyntax `tactic) :=
  `(tactic| norm_num $[at $hyp?:ident]?)


/--
Create a suggestion for `norm_cast`.

TODO: It seems that `push_cast` doesn't exist as a `conv` tactic,
  so we don't currently suggest it.
-/
public def suggestNormCast (e : Expr) (info : RewritingInfo) : MetaM Html :=
  mkLazyHtml do
  let e' := (← Lean.Elab.Tactic.NormCast.derive e).1
  renderRewritingTactic e e' info normCastSyntax `(conv| norm_cast)

section Algebra

/-- To avoid spawning a new thread if `e` is obviously not of the right form,
we do a quick check to see whether `e` is an application of an algebraic operation. -/
def isAlgebraicExpr (e : Expr) : MetaM Bool := do
  return (← whnfR e).getAppFn.constName matches
    ``HAdd.hAdd | ``Add.add |
    ``HMul.hMul | ``Mul.mul |
    ``HSMul.hSMul |
    ``HPow.hPow | ``Pow.pow |
    ``Neg.neg |
    ``HSub.hSub | ``Sub.sub |
    ``Inv.inv |
    ``HDiv.hDiv | ``Div.div

def runRingExpr (e : Expr) : MetaM Expr := do
  let e ← AtomM.run .reducible <| RingNF.evalExpr e
  return (← RingNF.cleanup {} e).expr

def runFieldExpr (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let disch := fun e ↦ Prod.fst <$> (FieldSimp.discharge e).run ctx >>= Option.getM
  return (← AtomM.run .reducible <| FieldSimp.reduceExpr disch e).expr

def runRingProp (e : Expr) : MetaM Expr := do
  let mkApp2 rel lhs rhs := e | failure
  let lhs ← runRingExpr lhs
  let rhs ← runRingExpr rhs
  return mkApp2 rel lhs rhs

def runFieldProp (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let disch := fun e ↦ Prod.fst <$> (FieldSimp.discharge e).run ctx >>= Option.getM
  return (← AtomM.run .reducible <| FieldSimp.reduceProp disch e).expr

/--
Create a suggestion for `ring_nf` and `field_simp` if applicable.

There are 2 cases where we may suggest this
1. The selected expression is an algebraic expression.
2. The selected expression is an equality or inequality of algebraic expressions.
-/
public def suggestAlgebraicNormalization (e : Expr) (info : RewritingInfo) : MetaM Html := do
  if ← isAlgebraicExpr e then
    mkLazyHtml do
    let mut htmls := #[]
    if let some e' ← try? <| runRingExpr e then
      if let some html ← renderRewritingTactic e e' info ringNFSyntax `(conv| ring_nf) then
        htmls := htmls.push html
    if let some e' ← try? <| runFieldExpr e then
      if let some html ← renderRewritingTactic e e' info fieldSimpSyntax `(conv| field_simp) then
        htmls := htmls.push html
    if htmls.isEmpty then
      return none
    return Html.element "div" #[] htmls
  else if ← succeeds (discard e.ineq?) then
    mkLazyHtml do
    let mut htmls := #[]
    if let some e' ← try? <| runRingProp e then
      if let some html ← renderRewritingTactic e e' info ringNFSyntax `(conv| ring_nf) then
        htmls := htmls.push html
    if let some e' ← try? <| runFieldProp e then
      if let some html ← renderRewritingTactic e e' info fieldSimpSyntax `(conv| field_simp) then
        htmls := htmls.push html
    if htmls.isEmpty then
      return none
    return Html.element "div" #[] htmls
  else
    return .text ""

end Algebra

section Simp

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
public def suggestSimp (e : Expr) (info : RewritingInfo) : MetaM Html :=
  mkLazyHtml do
  let mut htmls := #[]
  let e₁ ← runDSimpOnly e
  if let some html ← renderRewritingTactic e e₁ info dsimpOnlySyntax `(conv| dsimp only) then
    htmls := htmls.push html
  let e₂ ← runDSimp e
  if let some html ← renderRewritingTactic e₁ e₂ info dsimpSyntax `(conv| dsimp) then
    htmls := htmls.push html
  let e₃ ← runSimp e
  if let some html ← renderRewritingTactic e₂ e₃ info simpSyntax `(conv| simp) then
    htmls := htmls.push html
  let e₄ ← runNormNum e
  if let some html ← renderRewritingTactic e₃ e₄ info normNumSyntax `(conv| norm_num) then
    htmls := htmls.push html
  if htmls.isEmpty then
    return none
  return Html.element "div" #[] htmls

end Simp

end InfoviewSearch
