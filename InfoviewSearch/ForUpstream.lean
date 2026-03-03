/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import ProofWidgets.Data.Html
public import Lean.PrettyPrinter.Delaborator.Builtins

public section

namespace ProofWidgets

meta section

open Lean Widget PrettyPrinter.Delaborator Jsx

/-- Turn an `Expr` into an HTML with hover info. -/
def exprToHtml (e : Expr) : MetaM Html :=
  return <InteractiveCode fmt={← Widget.ppExprTagged e}/>

/-- Turn a constant into an HTML with hover info.
This avoids the `@` that may appear when using `exprToHtml`. -/
def constToHtml (n : Name) : MetaM Html := do
  let delab := withOptionAtCurrPos `pp.tagAppFns true <| delabConst
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppExprWithInfos (delab := delab) (← mkConstWithLevelParams n)
  let tt := TaggedText.prettyTagged fmt
  let ctx := {
    env           := (← getEnv)
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    fileMap       := default
    ngen          := (← getNGen)
  }
  return <InteractiveCode fmt={← tagCodeInfos ctx infos tt}/>

/-- Display `fmt` with a docstring as if it is the constant `n`. -/
def formatToHtmlWithDoc (fmt : Format) (n : Name) : MetaM Html := do
  let tag := 0
  -- Hack: use `.ofCommandInfo` instead of `.ofTacticInfo` to avoid printing `n` and its type.
  -- Unfortunately, there is still a loose dangling ` : `.
  let infos := .insert ∅ tag <| .ofCommandInfo
    { elaborator := `InfoviewSearch, stx := .node .none n #[] }
  let tt := TaggedText.prettyTagged <| .tag tag fmt
  let ctx := {
    env           := (← getEnv)
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    fileMap       := default
    ngen          := (← getNGen)
  }
  -- TODO: I would love to print this using the same keyword colour used by the editor,
  -- but I don't think this is possible. Additionally, `InteractiveCode` already overwrites the
  -- colour and style of the text (namely the expression style)
  return <InteractiveCode fmt={← tagCodeInfos ctx infos tt} />


/-- Pretty print a tactic with its docstring as hover info.

I would love to print `tac` with another colour, e.g. the keyword highlighting used by the editor,
but I have no idea how to do this.
-/
def tacticToHtml (tac : TSyntax `tactic) : MetaM Html := do
  formatToHtmlWithDoc (← PrettyPrinter.ppTactic tac) tac.1.getKind

end

end ProofWidgets

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
