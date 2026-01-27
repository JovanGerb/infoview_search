module

public import InfoviewSearch
import all InfoviewSearch.Search.FindCandidates
import Mathlib

public meta section

namespace InfoviewSearch
open Lean

def measureImport (choice : Choice) : MetaM (Nat × PreDiscrTrees) := do
  let t0 ← IO.monoMsNow
  let (tasks, _) ← foldEnv {} (Entries.addConst choice) 5000
  let pre : PreDiscrTrees := tasks.foldl (·.append ·.get) {}
  return ((← IO.monoMsNow) - t0, pre)

def loadAll : MetaM Unit := do
  let (rw, _) ← measureImport { rw := true, grw := false, app := false, appAt := false }
  let (grw, _) ← measureImport { rw := false, grw := true, app := false, appAt := false }
  let (apply, _) ← measureImport { rw := false, grw := false, app := true, appAt := false }
  let (applyAt, _) ← measureImport { rw := false, grw := false, app := false, appAt := true }
  let (all, _) ← measureImport { rw := true, grw := true, app := true, appAt := true }
  logInfo m!"rw: {rw}ms; grw: {grw}ms; apply: {apply}ms; apply at: {applyAt}ms\n\
    total: {all}ms"

-- run_meta loadAll

end InfoviewSearch
/-
Some example outputs I got:

rw: 3739ms; grw: 2256ms; apply: 3749ms; apply at: 2934ms
total: 8963ms

rw: 4181ms; grw: 2283ms; apply: 3934ms; apply at: 2812ms
total: 7760ms

rw: 3983ms; grw: 2196ms; apply: 3720ms; apply at: 2765ms
total: 9193ms

rw: 4105ms; grw: 2250ms; apply: 3685ms; apply at: 2997ms
total: 10960ms

---

rw: 5663ms; grw: 2071ms; apply: 4237ms; apply at: 2851ms
total: 8341ms

rw: 3484ms; grw: 2140ms; apply: 3671ms; apply at: 2836ms
total: 8821ms

-/
