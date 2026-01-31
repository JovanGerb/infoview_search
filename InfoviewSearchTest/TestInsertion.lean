module

public import InfoviewSearch.Util

meta section

open Lean Elab Server InfoviewSearch

def String.editText (file newText : String) (range : Lean.Syntax.Range) : String :=
    Pos.Raw.extract file {} range.start ++ newText ++
    Pos.Raw.extract file range.stop ⟨file.utf8ByteSize⟩

def String.highlightCursor (file : String) (cursorPos : String.Pos.Raw) : String :=
  file.editText "∣" ⟨cursorPos, cursorPos⟩

def testTacticInsertionLogic (tactic : CoreM (TSyntax `tactic))
    (cursorPosList : List Lsp.Position) (input : String) (onGoal : Option Nat := none) :
    CoreM Unit := do
  let context := Parser.mkInputContext input (fileName := "<input>")
  let s ← IO.processCommands context { : Parser.ModuleParserState } (Command.mkState (← getEnv))
  let trees : List InfoTree := s.commandState.infoState.trees.toList
  let text := context.fileMap
  for cursorPos in cursorPosList do
  let goalsAt := trees.flatMap (·.goalsAt? text (text.lspPosToUtf8Pos cursorPos))
  let input' := input.highlightCursor (text.lspPosToUtf8Pos cursorPos)
  if h : goalsAt.length = 0 then -- TODO: Use `goalsAt.isEmpty` instead
    logWarning m!"No goals found at{indentD input'}"
  else
    let pasteInfo := {
        «meta» := { (default : DocumentMeta) with text }
        cursorPos, onGoal
        stx := goalsAt[0].tacticInfo.stx }
    let (range, newText) ← mkInsertion (← tactic) pasteInfo
    let output := input.editText (newText ++ "|") (text.lspRangeToUtf8Range range)
    logInfo m!"Number of goals found: {goalsAt.length}\n\
      Before:{indentD <| input'}\n\
      After:{indentD <| output}"

/--
info: Number of goals found: 1
Before:
  example : 1 + 1 = 2 := ∣by
    skip
    skip
      ⏎
After:
  example : 1 + 1 = 2 := simp
                         |by
    skip
    skip
      ⏎
---
info: Number of goals found: 1
Before:
  example : 1 + 1 = 2 := by∣
    skip
    skip
      ⏎
After:
  example : 1 + 1 = 2 := bysimp
                           |
    skip
    skip
      ⏎
---
info: Number of goals found: 1
Before:
  example : 1 + 1 = 2 := by
    skip
    ∣skip
      ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    simp
    |skip
      ⏎
---
info: Number of goals found: 1
Before:
  example : 1 + 1 = 2 := by
    skip
    sk∣ip
      ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    sksimp
      |ip
      ⏎
---
info: Number of goals found: 1
Before:
  example : 1 + 1 = 2 := by
    skip
    skip∣
      ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    skipsimp
        |
      ⏎
---
info: Number of goals found: 1
Before:
  example : 1 + 1 = 2 := by
    skip
    skip
  ∣    ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    skip
  simp
  |    ⏎
---
info: Number of goals found: 1
Before:
  example : 1 + 1 = 2 := by
    skip
    skip
    ∣  ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    skip
    simp
    |  ⏎
---
info: Number of goals found: 1
Before:
  example : 1 + 1 = 2 := by
    skip
    skip
      ∣
After:
  example : 1 + 1 = 2 := by
    skip
    skip
      simp
      |
-/
#guard_msgs (whitespace := exact) in
run_meta
  testTacticInsertionLogic `(tactic| simp)
    [⟨0, 23⟩, ⟨0, 25⟩, ⟨2, 2⟩, ⟨2, 4⟩, ⟨2, 6⟩, ⟨3, 0⟩, ⟨3, 2⟩, ⟨3, 4⟩] "\
example : 1 + 1 = 2 := by
  skip
  skip
    "
