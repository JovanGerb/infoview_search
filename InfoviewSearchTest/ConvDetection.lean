import Lean

open Lean Elab Command Meta Tactic

/-!

Code to check if the current tactic state is in `conv` mode.

-/

def isConvMode : TacticM Bool :=
  return isLHSGoal? (← getMainTarget) |>.isSome

elab "is_conv?" : tactic => do
  let inConv ← isConvMode
  if inConv then
    logInfo "Currently in conv mode."
  else
    logInfo "Not in conv mode."

elab "is_conv?" : conv => do
  let inConv ← isConvMode
  if inConv then
    logInfo "Currently in conv mode."
  else
    logInfo "Not in conv mode."

example : 1 + 1 = 2 := by
  is_conv?
  rfl

example : 1 + 1 = 3 := by
  conv =>
    lhs
    is_conv?
    rw [Nat.add_comm]
  is_conv?
  sorry
