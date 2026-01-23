module

public import InfoviewSearch
import all InfoviewSearch
import Mathlib

public meta section

namespace InfoviewSearch.RefinedDiscrTree
open Lean Meta RefinedDiscrTree

@[inline]
def measureLoad {α} (load : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry)))) :
    MetaM Nat := do
  let env ← getEnv
  let ngen ← getNGen
  let (cNGen, ngen) := ngen.mkChild
  setNGen ngen
  let t0 ← IO.monoMsNow
  _ ← withTheReader Core.Context withTreeCtx do
    createImportedDiscrTree' cNGen env load 5000
  return (← IO.monoMsNow) - t0

def loadAll : MetaM Unit := do
  let rw ← measureLoad Rw.addRewriteEntry
  let grw ← measureLoad Grw.addGRewriteEntry
  let apply ← measureLoad Apply.addApplyEntry
  let applyAt ← measureLoad ApplyAt.addApplyAtEntry
  logInfo m!
    "rw: {rw}; grw: {grw}; apply: {apply}; apply at: {applyAt}\ntotal: {rw + grw + apply + applyAt}"
  if rw > 4000 then throwError "`rw` was too slow: {rw}ms"
  if grw > 2400 then throwError "`grw` was too slow: {grw}ms"
  if apply > 3000 then throwError "`apply` was too slow: {apply}ms"
  if applyAt > 3000 then throwError "`apply at` was too slow: {applyAt}ms"

run_meta loadAll
