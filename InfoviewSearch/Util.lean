/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import ProofWidgets.Component.MakeEditLink
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.NthRewrite
public import Mathlib.Tactic.DepRewrite
public import Batteries.Tactic.PermuteGoals
public import Mathlib.Data.String.Defs
public import InfoviewSearch.Conv
public import InfoviewSearch.RefreshComponent

public meta section

namespace InfoviewSearch

/-- Let the `#infoview_search` widget show all errors of lemmas that failed to apply. -/
register_option infoview_search.debug : Bool := {
  defValue := false
  descr := "let `#infoview_search` show all lemmas that were candidates, but which failed to apply"
}

open Lean Meta ProofWidgets Jsx Server

inductive Premise where
  | const (declName : Name)
  | fvar (fvarId : FVarId)
  deriving Inhabited

namespace Premise

def toString : Premise → String
  | .const name | .fvar ⟨name⟩ => name.toString

def length (premise : Premise) : Nat :=
  premise.toString.length

def getType : Premise → MetaM Expr
  | .const name => (·.type) <$> getConstInfo name
  | .fvar fvarId => fvarId.getType

def forallMetaTelescopeReducing : Premise → MetaM (Expr × Array Expr × Array BinderInfo × Expr)
  | .const name => do
    let thm ← mkConstWithFreshMVarLevels name
    let result ← Meta.forallMetaTelescopeReducing (← inferType thm)
    return (mkAppN thm result.1, result)
  | .fvar fvarId => do
    let decl ← fvarId.getDecl
    let result ← Meta.forallMetaTelescopeReducing (← instantiateMVars decl.type)
    return (mkAppN decl.toExpr result.1, result)

def unresolveName : Premise → MetaM Name
  | .const name => do
    unresolveNameGlobalAvoidingLocals name (fullNames := getPPFullNames (← getOptions))
  | .fvar fvarId => fvarId.getUserName

def toMessageData : Premise → MessageData
  | .const name => .ofConstName name
  | .fvar fvarId => .ofExpr (.fvar fvarId)

def toHtml (p : Premise) : MetaM Html :=
  return <InteractiveMessage msg={← WithRpcRef.mk (← addMessageContextFull (p.toMessageData))} />

end Premise

/-- The information required for pasting a suggestion into the editor -/
structure Context where
  /-- The current document -/
  «meta» : DocumentMeta
  /-- The range that should be replaced.
  In tactic mode, this should be the range of the suggestion tactic.
  In infoview mode, the start and end of the range should both be the cursor position. -/
  cursorPos : Lsp.Position
  /-- Whether to use the `on_goal n =>` combinator. -/
  onGoal : Option Nat
  /-- The preceding piece of syntax. This is used for merging consecutive `rw` tactics. -/
  stx : Syntax
  /-- The ongoing computations. This is used to inform the user. -/
  computations : IO.Ref (Std.TreeSet String)
  /-- The token for updating the HTML that represents the state of the ongoing computations. -/
  statusToken : RefreshToken
  /-- This use used by `ppTacticTagged`. -/
  ctx : Elab.ContextInfo
  /-- The main goal. -/
  goal : MVarId
  /-- The selected hypothesis, if any. -/
  hyp? : Option FVarId
  /-- The position of the selected subexpression. -/
  pos : SubExpr.Pos

abbrev InfoviewSearchM := ReaderT Context MetaM

private def rerenderStatus : InfoviewSearchM Unit := do
  let computations ← (← read).computations.get
  (← read).statusToken.refresh <|
    if computations.isEmpty then
      .text ""
    else
      -- TODO: use a fancier throbber instead of `⏳`?
      let title := "ongoing searches: " ++ String.intercalate ", " computations.toList;
      <span title={title}> {.text "⏳"} </span>

def asComputation {α} (name : String) (k : InfoviewSearchM α) : InfoviewSearchM α := do
  (← read).computations.modify (·.insert name)
  rerenderStatus
  try k
  finally
    (← read).computations.modify (·.erase name)
    rerenderStatus

def getHypIdent? : InfoviewSearchM (Option Ident) := do
  let some fvarId := (← read).hyp? | return none
  return mkIdent (← fvarId.getUserName)

def getHypIdent! : InfoviewSearchM Ident := do
  let some fvarId := (← read).hyp? | throwError "no hypothesis was selected"
  return mkIdent (← fvarId.getUserName)

section Meta

/-- Determine whether the explicit parts of two expressions are equal,
and the implicit parts are definitionally equal. -/
partial def isExplicitEq (t s : Expr) : MetaM Bool := do
  if t == s then
    return true
  unless t.getAppNumArgs == s.getAppNumArgs && t.getAppFn == s.getAppFn do
    return false
  let tArgs := t.getAppArgs
  let sArgs := s.getAppArgs
  let bis ← getBinderInfos t.getAppFn tArgs
  t.getAppNumArgs.allM fun i _ =>
    if bis[i]!.isExplicit then
      isExplicitEq tArgs[i]! sArgs[i]!
    else
      withNewMCtxDepth <| isDefEq tArgs[i]! sArgs[i]!
where
  /-- Get the `BinderInfo`s for the arguments of `mkAppN fn args`. -/
  getBinderInfos (fn : Expr) (args : Array Expr) : MetaM (Array BinderInfo) := do
    let mut fnType ← inferType fn
    let mut result := Array.mkEmpty args.size
    let mut j := 0
    for i in [:args.size] do
      unless fnType.isForall do
        fnType ← whnfD (fnType.instantiateRevRange j i args)
        j := i
      let .forallE _ _ b bi := fnType | throwError m! "expected function type {indentExpr fnType}"
      fnType := b
      result := result.push bi
    return result

end Meta

section Syntax
open Syntax Parser.Tactic

inductive RwKind where
| hasBVars
| valid (motiveTypeCorrect : Bool) (occ : Option Nat)

/-- Return syntax for the rewrite tactic `rw [e]`.
When `occ` is `none`, this means that `kabstract` cannot find the expression
due to bound variables, so in that case we fall back to `simp_rw`. -/
def mkRewrite (kind : RwKind) (symm : Bool) (e : Term) (loc : Option Ident)
    (grw := false) : CoreM (TSyntax `tactic) := do
  let rule ← if symm then `(Parser.Tactic.rwRule| ← $e) else `(Parser.Tactic.rwRule| $e:term)
  if grw then
    match kind with
    | .valid _ none => `(tactic| grw [$rule] $[at $loc:term]?)
    | .valid _ (some n) => `(tactic| nth_grw $(mkNatLit n):num [$rule] $[at $loc:term]?)
    -- We still lack a variant of `grw` that rewrites bound variables, so we just use `grw`.
    | .hasBVars => `(tactic| grw [$rule] $[at $loc:term]?)
  else
    match kind with
    | .valid true none => `(tactic| rw [$rule] $[at $loc:term]?)
    | .valid true (some n) => `(tactic| nth_rw $(mkNatLit n):num [$rule] $[at $loc:term]?)
    | .valid false none => `(tactic| rw! [$rule] $[at $loc:term]?)
    | .valid false (some n) =>
      let occs ← `(optConfig| ($(mkIdent `occs):ident := .$(mkIdent `pos) [$(mkNatLit n)]))
      `(tactic| rw! $occs [$rule] $[at $loc:term]?)
    | .hasBVars => `(tactic| simp_rw [$rule] $[at $loc:term]?)

def mergeTactics? {m} [Monad m] [MonadRef m] [MonadQuotation m] (stx₁ stx₂ : Syntax) :
    m (Option (TSyntax `tactic)) := do
  match stx₁, stx₂ with
  | `(tactic| rw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| rw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| rw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | `(tactic| simp_rw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| simp_rw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| simp_rw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | `(tactic| grw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| grw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| grw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | _, _ => pure ()
  return none

/-- Given tactic syntax `tac` that we want to paste into the editor, return it as a string.
This function respects the 100 character limit for long lines. -/
def tacticPasteString (tac : TSyntax `tactic) : InfoviewSearchM String := do
  let tac ← if let some n := (← read).onGoal then
      `(tactic| on_goal $(mkNatLit (n + 1)) => $(tac):tactic)
    else
      pure tac
  let column := (← read).cursorPos.character
  let indent := column
  return (← PrettyPrinter.ppTactic tac).pretty 100 indent column

/-- Given tactic syntax `tac`, compute the text edit that will paste it into the editor.
We return the range that should be replaced, and the new text that will replace it. -/
def mkInsertion (tac : TSyntax `tactic) : InfoviewSearchM (Lsp.Range × String) := do
  if let some tac ← mergeTactics? (← read).stx tac then
    if let some range := (← read).stx.getRange? then
      let text := (← read).meta.text
      let endPos := max (text.lspPosToUtf8Pos (← read).cursorPos) range.stop
      let extraWhitespace := range.stop.extract text.source endPos
      let tactic ← tacticPasteString tac (← read)
      return (text.utf8RangeToLspRange ⟨range.start, endPos⟩, tactic ++ extraWhitespace)
  return (⟨(← read).cursorPos, (← read).cursorPos⟩,
    s!"{← tacticPasteString tac (← read)}\n{String.replicate (← read).cursorPos.character ' '}")

end Syntax

section Widget

open Widget

def mkSuggestion (tac : TSyntax `tactic) (html : Html) (isText := false) :
    InfoviewSearchM Html := do
  let (range, newText) ← mkInsertion tac (← read)
  let button :=
    -- TODO: The hover on this button should be a `CodeWithInfos`, instead of a string.
    <span className="font-code"> {
      Html.ofComponent MakeEditLink
        (.ofReplaceRange (← read).meta range newText)
        #[<a
          className={"mh2 codicon codicon-insert"}
          style={json% { "position" : "relative", "top" : "0.15em"}}
          title={(← PrettyPrinter.ppTactic tac).pretty} />] }
    </span>;
  let html := if isText then <span style={json% { "margin-top" : "0.15em" }}> {html} </span>
    else html
  return <div display="flex"
    style={json% { "display" : "flex", "align-items" : "flex-start", "margin-bottom" : "1em" }}>
    {button} {html}
    </div>

def mkSuggestionList (htmls : Array Html) (header : Html) (startOpen := true) : Html :=
  <details «open»={startOpen}>
    <summary className="mv2 pointer"> {header} </summary>
    {.element "div" #[] htmls}
  </details>

/-- Display `str` with a docstring as if it is the constant `n`. -/
def ppWithDoc (str : String) (n : Name) : InfoviewSearchM CodeWithInfos := do
  let tag := 0
  -- Hack: use `.ofCommandInfo` instead of `.ofTacticInfo` to avoid printing `n` and its type.
  -- Unfortunately, there is still a loose dangling ` : `.
  let infos := .insert ∅ tag <| .ofCommandInfo { elaborator := `InfoviewSearch, stx := mkIdent n }
  let tt := TaggedText.prettyTagged <| .tag tag str
  -- TODO: I would love to print this using the keyword highlighting used by the editor,
  -- but I have no idea how to do this.
  tagCodeInfos (← read).ctx infos tt


/-- Pretty print a tactic with its docstring as hover info.

I would love to print `tac` with another colour, e.g. the keyword highlighting used by the editor,
but I have no idea how to do this.
-/
def ppTacticTagged (tac : TSyntax `tactic) : InfoviewSearchM CodeWithInfos := do
  let kind := tac.1.getKind
  let tac ← PrettyPrinter.ppTactic tac
  ppWithDoc tac.pretty kind

/-- Create a suggestion for inserting `stx` and tactic name `tac`. -/
def mkTacticSuggestion (stx tac : TSyntax `tactic) (html : Html) (isText := false) :
    InfoviewSearchM Html := do
  mkSuggestion stx (isText := isText) <div>
    <div>{html}</div>
    <div><InteractiveCode fmt={← ppTacticTagged tac}/></div>
    </div>

@[inline]
def mkIncrementalSuggestions (name : String) (k : (Html → BaseIO Unit) → InfoviewSearchM Unit) :
    InfoviewSearchM Html :=
  mkRefreshComponentM (.text "") fun token ↦ asComputation name do
    let htmls ← IO.mkRef #[]
    k fun html ↦ do
      htmls.modify (·.push html)
      token.refresh (Html.element "div" #[] (← htmls.get))


end Widget

def kabstractFindsPositions (e p : Expr) (targetPos : SubExpr.Pos) : MetaM Bool := do
  let e ← instantiateMVars e
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec
  /-- The main loop that loops through all subexpressions -/
  visit (e : Expr) (pos : SubExpr.Pos) :
      ExceptT Bool MetaM Unit := do
    let visitChildren (found := false) : ExceptT Bool MetaM Unit := do
      if pos == targetPos then
        throwThe _ found
      match e with
      | .app f a         => visit f pos.pushAppFn; visit a pos.pushAppArg
      | .mdata _ e       => visit e pos
      | .proj _ _ e      => visit e pos.pushProj
      | .letE _ t v b _  =>
        visit t pos.pushLetVarType; visit v pos.pushLetValue; visit b pos.pushLetBody
      | .lam _ d b _     => visit d pos.pushBindingDomain; visit b pos.pushBindingBody
      | .forallE _ d b _ => visit d pos.pushBindingDomain; visit b pos.pushBindingBody
      | _                => pure ()
    if e.hasLooseBVars then
      visitChildren
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren
    else
      if ← isDefEq e p then
        visitChildren true
      else
        visitChildren
  match ← ExceptT.run <| visit e .root with
  | .ok () => throwError "invalid position {targetPos} in {e}"
  | .error found => return found

end InfoviewSearch
