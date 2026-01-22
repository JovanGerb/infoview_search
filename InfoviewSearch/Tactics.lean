module

public import InfoviewSearch.Unfold

public meta section

namespace InfoviewSearch

open Lean Meta ProofWidgets

def mkUnusedNameNumbered (lctx : LocalContext) (name : Name) : Name :=
  if !lctx.usesUserName name then name else
  let name' := name.appendAfter "₁"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₂"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₃"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₄"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₅"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₆"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₇"
  if !lctx.usesUserName name' then name' else
  let name' := name.appendAfter "₈"
  if !lctx.usesUserName name' then name' else
  name.appendAfter "₉"

def renderIntro (loc : SubExpr.GoalsLocation) (pasteInfo : PasteInfo) : MetaM (Option Html) := do
  let .target pos := loc.loc | return none
  unless pos == .root do return none
  -- Only run `whnf` on the outer most type.
  -- If the user wants more `intro`, they can do that separately again.
  let goal ← loc.mvarId.getType'
  unless goal.isForall do return none
  forallTelescope goal fun xs _ ↦ do
    let text := match ← isProof xs[0]!, xs.size == 1 with
      | true, true => "introduce the hypothesis"
      | true, false => "introduce the hypotheses"
      | false, true => "introduce the variable"
      | false, false => "introduce the variables"
    let mut lctx ← getLCtx
    let mut names := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let name ← if ← isProp decl.type then pure `h else
        if decl.userName.hasMacroScopes then pure decl.userName.eraseMacroScopes
        else pure `x
      let name := mkUnusedNameNumbered lctx name
      names := names.push name
      lctx := lctx.setUserName x.fvarId! name
    let tactic ← `(tactic| intro $[$(names.map mkIdent)]*)
    mkSuggestionElement (isText := true) tactic pasteInfo <| .text text

def renderRfl (loc : SubExpr.GoalsLocation) (pasteInfo : PasteInfo) : MetaM (Option Html) := do
  let .target pos := loc.loc | return none
  unless pos == .root do return none
  let_expr Eq _ lhs rhs := ← instantiateMVars (← loc.mvarId.getType) | return none
  unless ← isDefEq lhs rhs do return none
  let tactic ← `(tactic| rfl)
  liftM <| mkSuggestionElement (isText := true) tactic pasteInfo <| .text "reflexivity"

def renderInduction (loc : SubExpr.GoalLocation) (pasteInfo : PasteInfo) : MetaM (Option Html) := do
  let .hyp fvarId := loc | return none
  let some typeHead := (← whnf (← fvarId.getType)).getAppFn.constName? | return none
  unless ← isInductive typeHead do return none
  let name ← fvarId.getUserName
  let mut usingClause := none
  let elims ← getCustomEliminators
  if !elims.map.contains (true, #[typeHead]) then
    if (← getEnv).contains (typeHead.str "induction") then
      usingClause := some (mkIdent (typeHead.str "induction"))
  let tactic ← `(tactic| induction $(mkIdent name):ident $[using $usingClause]?)
  mkSuggestionElement (isText := true) ⟨tactic.1⟩ pasteInfo <| .text s!"induction on {name}"

def renderTactic (e : Expr) (occ : Option Nat) (location : Option Name)
    (loc : SubExpr.GoalsLocation) (pasteInfo : PasteInfo) : MetaM (Array Html) := do
  let mut tactics := #[]
  if let some html ← renderRfl loc pasteInfo then
    tactics := tactics.push html
  if let some html ← renderInduction loc.loc pasteInfo then
    tactics := tactics.push html
  if let some html ← renderIntro loc pasteInfo then
    tactics := tactics.push html
  let mut htmls := #[]
  if !tactics.isEmpty then
    htmls := htmls.push <| mkListElement tactics <| .text "tactics"
  if let some html ← InteractiveUnfold.renderUnfolds e occ location pasteInfo then
    htmls := htmls.push html
  return htmls

end InfoviewSearch
