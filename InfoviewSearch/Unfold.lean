/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import InfoviewSearch.Util
public import Mathlib.Tactic.Widget.SelectPanelUtils

/-!

# Interactive unfolding

This file defines the interactive tactic `unfold?`.
It allows you to shift-click on an expression in the goal, and then it suggests rewrites to replace
the expression with an unfolded version.

It can be used on its own, but it can also be used as part of the library rewrite tactic `rw??`,
where these unfoldings are a subset of the suggestions.

For example, if the goal contains `1+1`, then it will suggest rewriting this into one of
- `Nat.add 1 1`
- `2`

Clicking on a suggestion pastes a rewrite into the editor, which will be of the form
- `rw [show 1+1 = Nat.add 1 1 from rfl]`
- `rw [show 1+1 = 2 from rfl]`
It also takes into account the position of the selected expression if it appears in multiple places,
and whether the rewrite is in the goal or a local hypothesis.
The rewrite string is created using `mkRewrite`.

## Reduction rules

The basic idea is to repeatedly apply `unfoldDefinition?` followed by `whnfCore`, which gives
the list of all suggested unfoldings. Each suggested unfolding is in `whnfCore` normal form.

Additionally, eta-reduction is tried, and basic natural number reduction is tried.

## Filtering

`HAdd.hAdd` in `1+1` actually first unfolds into `Add.add`, but this is not very useful,
because this is just unfolding a notational type class. Therefore, unfoldings of default instances
are not presented in the list of suggested rewrites.
This is implemented with `unfoldProjDefaultInst?`.

Additionally, we don't want to unfold into expressions involving `match` terms or other
constants marked as `Name.isInternalDetail`. So all such results are filtered out.
This is implemented with `isUserFriendly`.

-/

public meta section

open Lean Meta Server Widget ProofWidgets Jsx

namespace InfoviewSearch.InteractiveUnfold

set_option linter.style.emptyLine false in
/-- Unfold a class projection if the instance is tagged with `@[default_instance]`.
This is used in the `unfold?` tactic in order to not show these unfolds to the user.
Similar to `Lean.Meta.unfoldProjInst?`. -/
def unfoldProjDefaultInst? (e : Expr) : MetaM (Option Expr) := do
  let .const declName _ := e.getAppFn | return none
  let some { fromClass := true, ctorName, .. } ← getProjectionFnInfo? declName | return none
  -- get the list of default instances of the class
  let some (ConstantInfo.ctorInfo ci) := (← getEnv).find? ctorName | return none
  let defaults ← getDefaultInstances ci.induct
  if defaults.isEmpty then return none

  let some e ← withDefault <| unfoldDefinition? e | return none
  let .proj _ i c := e.getAppFn | return none
  -- check that the structure `c` comes from one of the default instances
  let .const inst _ := c.getAppFn | return none
  unless defaults.any (·.1 == inst) do return none

  let some r ← withReducibleAndInstances <| project? c i | return none
  return mkAppN r e.getAppArgs |>.headBeta

/-- Return the consecutive unfoldings of `e`. -/
partial def unfolds (e : Expr) : MetaM (Array Expr) := do
  let e' ← whnfCore e
  go e' (if e == e' then #[] else #[e'])
where
  /-- Append the unfoldings of `e` to `acc`. Assume `e` is in `whnfCore` form. -/
  go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) :=
    tryCatchRuntimeEx
      (withIncRecDepth do
        if let some e := e.etaExpandedStrict? then
          let e ← whnfCore e
          return ← go e (acc.push e)
        if let some e ← reduceNat? e then
          return acc.push e
        if let some e ← reduceNative? e then
          return acc.push e
        if let some e ← unfoldProjDefaultInst? e then
          -- when unfolding a default instance, don't add it to the array of unfolds.
          let e ← whnfCore e
          return ← go e acc
        if let some e ← unfoldDefinition? e then
          -- Note: whnfCore can give a recursion depth error
          let e ← whnfCore e
          return ← go e (acc.push e)
        return acc)
      fun _ =>
        return acc

/-- Determine whether `e` contains no internal names. -/
partial def isUserFriendly (e : Expr) : MetaM Bool := do
  match e with
  | .const name _ => return !name.isInternalDetail
  | .proj .. => return false
  | .app .. =>
    e.withApp fun f args => do
    (isUserFriendly f) <&&> do
      let finfo ← getFunInfoNArgs f e.getAppNumArgs
      e.getAppNumArgs.allM fun i _ =>
        if finfo.paramInfo[i]?.all (·.isExplicit) then isUserFriendly args[i]! else return true
  | _ => return true

/-- Return the consecutive unfoldings of `e` that are user friendly. -/
def filteredUnfolds (e : Expr) : MetaM (Array Expr) := do
  (← unfolds e).filterM isUserFriendly

/-- Return the tactic string that does the unfolding. -/
def tacticSyntax (e eNew : Expr) (rwKind : RwKind) (hyp? : Option Name) :
    MetaM (TSyntax `tactic) := do
  let e ← PrettyPrinter.delab e
  let eNew ← PrettyPrinter.delab eNew
  let fromRfl ← `(show $e = $eNew from $(mkIdent `rfl))
  mkRewrite rwKind false fromRfl hyp?

/-- Render the unfolds of `e` as given by `filteredUnfolds`, with buttons at each suggestion
for pasting the rewrite tactic. Return `none` when there are no unfolds. -/
def renderUnfolds (e : Expr) (rwKind : RwKind) (hyp? : Option Name) :
    InfoviewSearchM (Option Html) := do
  let results ← filteredUnfolds e
  if results.isEmpty then
    return none
  let htmls ← results.mapM fun unfold => do
    let tactic ← tacticSyntax e unfold rwKind hyp?
    mkSuggestion tactic <InteractiveCode fmt={← ppExprTagged unfold}/>
  return mkListElement (startOpen := false) htmls <| .text "unfold"

end InfoviewSearch.InteractiveUnfold
