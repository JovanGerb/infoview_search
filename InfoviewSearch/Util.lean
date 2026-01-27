module

public import ProofWidgets.Component.MakeEditLink
public import ProofWidgets.Component.OfRpcMethod
public import ProofWidgets.Data.Html
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.NthRewrite
public meta import Mathlib.Lean.Meta.RefinedDiscrTree
public import Batteries.Tactic.PermuteGoals

public meta section

namespace InfoviewSearch

open Lean Meta Widget ProofWidgets Jsx Server

initialize
  registerTraceClass `infoview_search

instance {α} : Append (RefinedDiscrTree.MatchResult α) where
  append a b := ⟨a.elts.mergeWith (fun _ a b => a ++ b) b.elts⟩

def _root_.Lean.Meta.RefinedDiscrTree.MatchResult.map {α β} (f : α → β)
    (r : RefinedDiscrTree.MatchResult α) : RefinedDiscrTree.MatchResult β :=
  ⟨r.elts.map fun _ a => a.map (·.map f)⟩

/-- The kind of library lemma -/
inductive PremiseKind where
  /-- A local hypothesis -/
  | hypothesis
  /-- A lemma from the current file -/
  | fromFile
  /-- A lemma from an imported file -/
  | fromImport

inductive Premise where
  | const (declName : Name)
  | fvar (fvarId : FVarId)
  deriving Inhabited

namespace Premise

def toString : Premise → String
  | .const name | .fvar ⟨name⟩ => name.toString

def length (premise : Premise) : Nat :=
  premise.toString.length

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

end Premise

/-- Pretty print the given constant, making sure not to print the `@` symbol.
This is a HACK and there should be a more principled way to do this. -/
def ppConstTagged (name : Name) : MetaM CodeWithInfos := do
  return match ← ppExprTagged (← mkConstWithLevelParams name) with
    | .tag tag _ => .tag tag (.text s!"{name}")
    | code => code

def ppPremiseTagged : Premise → MetaM CodeWithInfos
  | .const name => ppConstTagged name
  | .fvar fvarId => ppExprTagged (.fvar fvarId)

/-- The information required for pasting a suggestion into the editor -/
structure PasteInfo where
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

/-- Return syntax for the rewrite tactic `rw [e]`.
When `occ` is `none`, this means that `kabstract` cannot find the expression
due to bound variables, so in that case we fall back to `simp_rw`. -/
def mkRewrite (occ : LOption Nat) (symm : Bool) (e : Term) (loc : Option Name)
    (grw := false) : CoreM (TSyntax `tactic) := do
  let loc := loc.map mkIdent
  let rule ← if symm then `(Parser.Tactic.rwRule| ← $e) else `(Parser.Tactic.rwRule| $e:term)
  match occ, grw with
  | .some n, false => `(tactic| nth_rw $(Syntax.mkNatLit n):num [$rule] $[at $loc:term]?)
  | .none, false => `(tactic| rw [$rule] $[at $loc:term]?)
  | .undef, false => `(tactic| simp_rw [$rule] $[at $loc:term]?)
  | .some n, true => `(tactic| nth_grw $(Syntax.mkNatLit n):num [$rule] $[at $loc:term]?)
  -- We currently lack a variant of `grw` that rewrites bound variables, so we just use `grw`.
  | _, true => `(tactic| grw [$rule] $[at $loc:term]?)

/-- Get the `BinderInfo`s for the arguments of `mkAppN fn args`. -/
def getBinderInfos (fn : Expr) (args : Array Expr) : MetaM (Array BinderInfo) := do
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
def tacticPasteString (tac : TSyntax `tactic) (pasteInfo : PasteInfo) : CoreM String := do
  let tac ← if let some n := pasteInfo.onGoal then
      `(tactic| on_goal $(Syntax.mkNatLit (n + 1)) => $(tac):tactic)
    else
      pure tac
  let column := pasteInfo.cursorPos.character
  let indent := column
  return (← PrettyPrinter.ppTactic tac).pretty 100 indent column

def mkSuggestionElement (tac : TSyntax `tactic) (pasteInfo : PasteInfo)
    (html : Html) (isText := false) : CoreM Html := do
  let singleTactic ← tacticPasteString tac pasteInfo
  let (tactic, replaceRange) ← (do
    if let some tac ← mergeTactics? pasteInfo.stx tac then
      if let some range := pasteInfo.stx.getRange? then
        let text := pasteInfo.meta.text
        let endPos := max (text.lspPosToUtf8Pos pasteInfo.cursorPos) range.stop
        let extraWhitespace := range.stop.extract text.source endPos
        let tactic ← tacticPasteString tac pasteInfo
        return (tactic ++ extraWhitespace, text.utf8RangeToLspRange ⟨range.start, endPos⟩)
    return (s!"{singleTactic}\n{String.ofList (.replicate pasteInfo.cursorPos.character ' ')}",
      ⟨pasteInfo.cursorPos, pasteInfo.cursorPos⟩))
  let button :=
    -- TODO: The hover on this button should be a `CodeWithInfos`, instead of a string.
    <span className="font-code"> {
      Html.ofComponent MakeEditLink
        (.ofReplaceRange pasteInfo.meta replaceRange tactic)
        #[<a
          className={"mh2 codicon codicon-insert"}
          style={json% { "position" : "relative", "top" : "0.15em"}}
          title={singleTactic} />] }
    </span>;
  let html :=
    if isText then <div style={json% { "margin-top" : "0.15em" }}> {html} </div> else html;
  return <li
      style={json% { "display" : "flex", "align-items" : "flex-start", "margin-bottom" : "1em" }}>
    {button}
    {html}
  </li>

def mkListElement (htmls : Array Html) (header : Html) (startOpen := true) : Html :=
  <details «open»={startOpen}>
    <summary className="mv2 pointer"> {header} </summary>
    {.element "ul" #[("style", json% { "padding-left" : "0", "list-style" : "none"})] htmls}
  </details>

structure ExprWithPos where
  /-- The root Expression. -/
  root : Expr
  /-- The position of within the root expression. -/
  targetPos  : SubExpr.Pos

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

section MonadDrop

/--
The class `MonadDrop m n` allows a computation in monad `m` to be run in monad `n`.
For example, a `MetaM` computation can be ran in `EIO Exception`,
which can then be ran as a task using `EIO.asTask`.
-/
class MonadDrop (m : Type → Type) (n : outParam <| Type → Type) where
  /-- Translates an action from monad `m` into monad `n`. -/
  dropM {α} : m α → m (n α)

export MonadDrop (dropM)

variable {m n : Type → Type} [Monad m] [MonadDrop m n]

instance : MonadDrop m m where
  dropM := pure

instance {ρ} : MonadDrop (ReaderT ρ m) n where
  dropM act := fun ctx => dropM (act ctx)

instance {σ} : MonadDrop (StateT σ m) n where
  dropM act := do liftM <| dropM <| act.run' (← get)

instance {ω σ} [MonadLiftT (ST ω) m] : MonadDrop (StateRefT' ω σ m) n where
  dropM act := do liftM <| dropM <| act.run' (← get)

end MonadDrop
