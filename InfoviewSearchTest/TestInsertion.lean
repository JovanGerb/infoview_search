module

public import InfoviewSearch.Util

public meta section

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
  let findSyntax (pos : String.Pos.Raw) : Option Syntax :=
    trees.findSome? (·.goalsAt? text pos |>.head?) |>.map (·.tacticInfo.stx)
  for cursorPos in cursorPosList do
    -- logInfo m!"{trees.flatMap (·.goalsAt? text (text.lspPosToUtf8Pos cursorPos))
    --   |>.map (repr ·.tacticInfo.stx)}"
    let input' := input.highlightCursor (text.lspPosToUtf8Pos cursorPos)
    let some stx := findSyntax (text.lspPosToUtf8Pos cursorPos) |
      logWarning m!"No goals found at{indentD input'}"
    -- logInfo m!"{repr stx}, {stx}"
    let pasteInfo ← PasteInfo.new
      { (default : DocumentMeta) with text } cursorPos onGoal stx findSyntax
    let (range, newText) ← mkInsertion (← tactic) pasteInfo
    let output := input.editText (newText ++ "∣") (text.lspRangeToUtf8Range range)
    logInfo m!"\
      Before:{indentD <| input'}\n\
      After:{indentD <| output}"

/--
info: Before:
  example : 1 + 1 = 2 := ∣by
    skip
    skip
      ⏎
After:
  example : 1 + 1 = 2 := by
    simp∣
    skip
    skip
      ⏎
---
info: Before:
  example : 1 + 1 = 2 := by∣
    skip
    skip
      ⏎
After:
  example : 1 + 1 = 2 := by
    simp∣
    skip
    skip
      ⏎
---
info: Before:
  example : 1 + 1 = 2 := by
  ∣  skip
    skip
      ⏎
After:
  example : 1 + 1 = 2 := by
    simp
  ∣  skip
    skip
      ⏎
---
info: Before:
  example : 1 + 1 = 2 := by
    ∣skip
    skip
      ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    simp∣
    skip
      ⏎
---
info: Before:
  example : 1 + 1 = 2 := by
    skip
  ∣  skip
      ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    simp
  ∣  skip
      ⏎
---
info: Before:
  example : 1 + 1 = 2 := by
    skip
    ∣skip
      ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    skip
    simp∣
      ⏎
---
info: Before:
  example : 1 + 1 = 2 := by
    skip
    sk∣ip
      ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    skip
    simp∣
      ⏎
---
info: Before:
  example : 1 + 1 = 2 := by
    skip
    skip∣
      ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    skip
    simp∣
      ⏎
---
info: Before:
  example : 1 + 1 = 2 := by
    skip
    skip
  ∣    ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    skip
    simp
  ∣    ⏎
---
info: Before:
  example : 1 + 1 = 2 := by
    skip
    skip
    ∣  ⏎
After:
  example : 1 + 1 = 2 := by
    skip
    skip
    simp
    ∣  ⏎
---
info: Before:
  example : 1 + 1 = 2 := by
    skip
    skip
      ∣
After:
  example : 1 + 1 = 2 := by
    skip
    skip
    simp
      ∣
-/
#guard_msgs (whitespace := exact) in
run_meta
  testTacticInsertionLogic `(tactic| simp)
    [⟨0, 23⟩, ⟨0, 25⟩, ⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 4⟩, ⟨2, 6⟩, ⟨3, 0⟩, ⟨3, 2⟩, ⟨3, 4⟩] "\
example : 1 + 1 = 2 := by
  skip
  skip
    "

/--
info: Before:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
  ∣  | zero =>
      ·
    | succ n ih =>
  ⏎
After:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
    simp
  ∣  | zero =>
      ·
    | succ n ih =>
  ⏎
---
info: Before:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
    ∣| zero =>
      ·
    | succ n ih =>
  ⏎
After:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
    | zero =>
      simp∣
      ·
    | succ n ih =>
  ⏎
---
info: Before:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
    | ∣zero =>
      ·
    | succ n ih =>
  ⏎
After:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
    | zero =>
      simp∣
      ·
    | succ n ih =>
  ⏎
---
info: Before:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
    | zero =>∣
      ·
    | succ n ih =>
  ⏎
After:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
    | zero =>
      simp∣
      ·
    | succ n ih =>
  ⏎
---
info: Before:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
    | zero =>
      ∣·
    | succ n ih =>
  ⏎
After:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
    | zero =>
      · simp∣
    | succ n ih =>
  ⏎
---
info: Before:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
    | zero =>
      ·
  ∣  | succ n ih =>
  ⏎
After:
  example (n : Nat) : 1 + 1 = 2 := by
    skip
    induction n with
    | zero =>
      ·
    simp
  ∣  | succ n ih =>
-/
#guard_msgs (whitespace := exact) in
run_meta
  testTacticInsertionLogic `(tactic| simp)
    [ ⟨3, 0⟩, ⟨3, 2⟩, ⟨3, 4⟩, ⟨3, 11⟩, ⟨4, 4⟩, ⟨4, 6⟩] "\
example (n : Nat) : 1 + 1 = 2 := by
  skip
  induction n with
  | zero =>
    ·
  | succ n ih =>
"
