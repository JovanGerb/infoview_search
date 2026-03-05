/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Lean.Linter.Deprecated
public import Lean.Meta.LazyDiscrTree

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

/--
Run `act name constInfo`.

Note: It is expensive to create two new `IO.Ref`s for every `MetaM` operation,
  so instead we reuse the same refs `mstate` and `cstate`. These are also used to
  remember the cache, and the name generator across the operations.
-/
@[inline]
private def visitConst (env : Environment) (modName : Name) (errorRef : ImportErrorRef)
    (act : α → Environment → Name → ConstantInfo → MetaM α)
    (a : α) (name : Name) (constInfo : ConstantInfo) : MetaM α := do
  try
    act a env name constInfo
  catch e =>
    let i : ImportFailure := {
      module := modName,
      const := name,
      exception := e }
    errorRef.errors.modify (·.push i)
    return a

/-- Loop through all constants in modules with module index from `start` to `stop - 1`. -/
@[specialize]
private def foldModules (ngen : NameGenerator) (errorRef : ImportErrorRef)
    (env : Environment) (init : α) (act : α → Environment → Name → ConstantInfo → MetaM α)
    (mctx : Meta.Context) (cctx : Core.Context)
    (start stop : Nat) : EIO Exception α := do
  let go : MetaM α := do
    let mut a := init
    for i in start...stop do
      Core.checkInterrupted
      let modName := env.header.moduleNames[i]!
      let { constNames, constants, .. } := env.header.moduleData[i]!
      for h : i in *...constNames.size do
        let name := constNames[i]
        let constInfo := constants[i]!
        a ← visitConst env modName errorRef act a name constInfo
    return a
  go.run' mctx {} |>.run' cctx { env, ngen }

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
@[specialize]
def foldEnv (init : α) (cfg : Config) (act : α → Environment → Name → ConstantInfo → MetaM α)
    (constantsPerTask : Nat := 5000) : CoreM (Array (Task (Except Exception α)) × ImportErrorRef) := do
  let env ← getEnv
  let numModules := env.header.moduleData.size
  let mctx := { keyedConfig := cfg.toConfigWithKey }
  let cctx := { (← read) with maxHeartbeats := 0 }
  let errorRef ← ImportErrorRef.new
  let rec
    /-- Allocate constants to tasks according to `constantsPerTask`. -/
    @[specialize]
    go (tasks : Array (Task (Except Exception α))) (start cnt idx : Nat) :
        CoreM (Array (Task (Except Exception α))) := do
      if h : idx < numModules then
        let mdata := env.header.moduleData[idx]
        let cnt := cnt + mdata.constants.size
        if cnt > constantsPerTask then
          let ngen ← getChildNgen
          let t ← (foldModules ngen errorRef env init act mctx cctx start (idx+1)).asTask
          go (tasks.push t) (idx+1) 0 (idx+1)
        else
          go tasks start cnt (idx+1)
      else
        if start < numModules then
          let ngen ← getChildNgen
          let t ← (foldModules ngen errorRef env init act mctx cctx start numModules).asTask
          pure (tasks.push t)
        else
          pure tasks
    termination_by env.header.moduleData.size - idx
  return (← go #[] 0 0 0, errorRef)

@[specialize]
def foldCurrModule (init : α) (cfg : Config) (act : α → Environment → Name → ConstantInfo → MetaM α) :
    CoreM (α × ImportErrorRef) := do
  let env ← getEnv
  let modName := env.header.mainModule
  let errorRef ← ImportErrorRef.new
  let ngen ← getChildNgen
  let go : MetaM α := env.constants.map₂.foldlM (visitConst env modName errorRef act) init
  let result ← go.run' { keyedConfig := cfg.toConfigWithKey } {}
    |>.run' { (← read) with maxHeartbeats := 0 } { env, ngen }
  return (result, errorRef)

end InfoviewSearch
