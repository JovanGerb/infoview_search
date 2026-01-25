/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Lean.Meta.CompletionName
public import Lean.Linter.Deprecated

/-!
# Looping through the environment efficietly, using paralellism
-/

public section

namespace InfoviewSearch
open Lean Meta

variable {α : Type}

/-- Information about a failed import. -/
structure ImportFailure where
  /-- Module containing the constant whose import failed. -/
  module : Name
  /-- Constant whose import failed. -/
  const : Name
  /-- Exception that triggered the error. -/
  exception : Exception

/-- Information generated from imported modules. -/
structure ImportErrorRef where
  errors : IO.Ref (Array ImportFailure)

def ImportErrorRef.new : BaseIO ImportErrorRef := do
  return { errors := ← IO.mkRef #[] }

/-- Return true if `declName` is automatically generated,
or otherwise unsuitable as a lemma suggestion. -/
def blacklistInsertion (env : Environment) (declName : Name) : Bool :=
  declName.isInternalDetail ||
  declName.isMetaprogramming ||
  !allowCompletion env declName ||
  Linter.isDeprecated env declName ||
  declName == ``sorryAx ||
  (declName matches .str _ "inj" | .str _ "injEq" | .str _ "sizeOf_spec")

private def MetaContext : Meta.Context where
  keyedConfig := Config.toConfigWithKey { transparency := .reducible }

/--
Run `act name constInfo`.

Note: It is expensive to create two new `IO.Ref`s for every `MetaM` operation,
  so instead we reuse the same refs `mstate` and `cstate`. These are also used to
  remember the cache, and the name generator across the operations.
-/
@[inline] private def visitConst
    (cctx : Core.Context)
    (env : Environment)
    (modName : Name)
    (errorRef : ImportErrorRef)
    (mstate : IO.Ref Meta.State)
    (cstate : IO.Ref Core.State)
    (act : α → Name → ConstantInfo → MetaM α)
    (a : α) (name : Name) (constInfo : ConstantInfo) :
    BaseIO α := do
  -- here we use an if-then-else clause instead of the more stylish if-then-return,
  -- because it compiles to more performant code
  if constInfo.isUnsafe then pure a else
  if blacklistInsertion env name then pure a else
  match ← (((act a name constInfo) MetaContext mstate) cctx cstate).toBaseIO with
  | .ok a => return a
  | .error e =>
    let i : ImportFailure := {
      module := modName,
      const := name,
      exception := e }
    errorRef.errors.modify (·.push i)
    return a

/-- Loop through all constants that appear in the module `mdata`. -/
private def visitModule
    (cctx : Core.Context)
    (env : Environment)
    (errorRef : ImportErrorRef)
    (mstate : IO.Ref Meta.State)
    (cstate : IO.Ref Core.State)
    (act : α → Name → ConstantInfo → MetaM α)
    (mname : Name)
    (constNames : Array Name) (constants : Array ConstantInfo)
    (a : α) : BaseIO α := do
  let mut a := a
  for h : i in *...constNames.size do
    let name := constNames[i]
    let constInfo := constants[i]!
    a ← visitConst cctx env mname errorRef mstate cstate act a name constInfo
  return a

/-- Loop through all constants in modules with module index from `start` to `stop - 1`. -/
private def foldModules (cctx : Core.Context) (ngen : NameGenerator) (errorRef : ImportErrorRef)
    (env : Environment) (init : α) (act : α → Name → ConstantInfo → MetaM α)
    (start stop : Nat) : BaseIO α := do
  let mstate ← IO.mkRef {}
  let cstate ← IO.mkRef { env, ngen }
  let mut a := init
  for i in start...stop do
    let mname := env.header.moduleNames[i]!
    let mdata := env.header.moduleData[i]!
    a ← visitModule cctx env errorRef mstate cstate act
      mname mdata.constNames mdata.constants a
  return a

private def getChildNgen : CoreM NameGenerator := do
  let ngen ← getNGen
  let (cngen, ngen) := ngen.mkChild
  setNGen ngen
  pure cngen

def logImportFailures (ref : ImportErrorRef) : CoreM Unit := do
  (← ref.errors.get).forM fun f ↦
    logError m!"Processing failure with {f.const} in {f.module}:\n  {f.exception.toMessageData}"

/-- Fold through all imported constants using `act`.
This uses paralellism, with each thread independently folding over part of the environment.
Hence, the result is given as an array of tasks, which can the be combined using `Array.foldl`. -/
def foldEnv (init : α) (act : α → Name → ConstantInfo → MetaM α) (constantsPerTask : Nat) :
    CoreM (Array (Task α) × ImportErrorRef) := do
  let env ← getEnv
  let numModules := env.header.moduleData.size
  let ctx := { (← read) with maxHeartbeats := 0 }
  let errorRef ← ImportErrorRef.new
  let rec
    /-- Allocate constants to tasks according to `constantsPerTask`. -/
    go (tasks : Array (Task α)) (start cnt idx : Nat) : CoreM (Array (Task α)) := do
      if h : idx < numModules then
        let mdata := env.header.moduleData[idx]
        let cnt := cnt + mdata.constants.size
        if cnt > constantsPerTask then
          let ngen ← getChildNgen
          let t ← (foldModules ctx ngen errorRef env init act start (idx+1)).asTask
          go (tasks.push t) (idx+1) 0 (idx+1)
        else
          go tasks start cnt (idx+1)
      else
        if start < numModules then
          let ngen ← getChildNgen
          let t ← (foldModules ctx ngen errorRef env init act start numModules).asTask
          pure (tasks.push t)
        else
          pure tasks
    termination_by env.header.moduleData.size - idx
  return (← go #[] 0 0 0, errorRef)

def foldCurrModule (init : α) (act : α → Name → ConstantInfo → MetaM α) :
    CoreM (α × ImportErrorRef) := do
  let env ← getEnv
  let modName := env.header.mainModule
  let ctx := { (← read) with maxHeartbeats := 0 }
  let errorRef ← ImportErrorRef.new
  let ngen ← getChildNgen
  let mstate ← IO.mkRef {}
  let cstate ← IO.mkRef { env, ngen }
  let result ← liftM <| env.constants.map₂.foldlM (init := init)
    (visitConst ctx env modName errorRef mstate cstate act)
  return (result, errorRef)

end InfoviewSearch
