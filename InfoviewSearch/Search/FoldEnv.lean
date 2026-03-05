/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Lean.Meta.Basic
public import Mathlib.Init

/-!
# Folding through the environment efficiently

This file defines `foldEnv`, a function for efficiently folding through the environment.
It splits the environment into parts, each is folded over in a separate thread.

We also provide `foldCurrModule` which loops through the declarations of the current module,
without any parallellism.
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
  errors : IO.Ref (List ImportFailure)

def ImportErrorRef.new : BaseIO ImportErrorRef := do
  return { errors := ← IO.mkRef [] }

def logImportFailures (ref : ImportErrorRef) : CoreM Unit := do
  (← ref.errors.get).forM fun f ↦
    logError m!"Processing failure with {f.const} in {f.module}:\n  {f.exception.toMessageData}"

/-- Run `act env name constInfo`, catching potential errors. -/
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
    errorRef.errors.modify (i :: ·)
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

/-- Fold through all imported constants using `act`.
This uses paralellism, with each thread independently folding over part of the environment.
Hence, the result is given as an array of tasks, which can then be combined using `Array.foldl`. -/
@[specialize]
def foldEnv (init : α) (cfg : Config) (act : α → Environment → Name → ConstantInfo → MetaM α)
    (constantsPerTask : Nat := 5000) :
    CoreM (Array (Task (Except Exception α)) × ImportErrorRef) := do
  let env ← getEnv
  let numModules := env.header.moduleData.size
  let mctx := { keyedConfig := cfg.toConfigWithKey }
  let cctx := { (← read) with maxHeartbeats := 0 }
  let errorRef ← ImportErrorRef.new
  let mut tasks := #[]
  let mut start := 0
  let mut count := 0
  for h : idx in *...numModules do
    count := count + env.header.moduleData[idx].constants.size
    if count > constantsPerTask then
      let (childNGen, parentNGen) := (← getNGen).mkChild
      setNGen parentNGen
      let t ← (foldModules childNGen errorRef env init act mctx cctx start (idx+1)).asTask
      tasks := tasks.push t
      count := 0
      start := idx + 1
  if start < numModules then
    let (childNGen, parentNGen) := (← getNGen).mkChild
    setNGen parentNGen
    let t ← (foldModules childNGen errorRef env init act mctx cctx start numModules).asTask
    tasks := tasks.push t
  return (tasks, errorRef)

@[specialize]
def foldCurrModule (init : α) (cfg : Config)
    (act : α → Environment → Name → ConstantInfo → MetaM α) : CoreM (α × ImportErrorRef) := do
  let env ← getEnv
  let modName := env.header.mainModule
  let errorRef ← ImportErrorRef.new
  let (childNGen, parentNGen) := (← getNGen).mkChild
  setNGen parentNGen
  let go : MetaM α := env.constants.map₂.foldlM (visitConst env modName errorRef act) init
  let result ← go.run' { keyedConfig := cfg.toConfigWithKey } {}
    |>.run' { (← read) with maxHeartbeats := 0 } { env, ngen := childNGen }
  return (result, errorRef)

end InfoviewSearch
