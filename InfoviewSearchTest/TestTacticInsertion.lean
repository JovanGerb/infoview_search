module

public import Lean
public import InfoviewSearch.Util

meta section

open Lean Elab Command Meta Tactic Server InfoviewSearch

def String.Pos.Raw.toPos (offset : String.Pos.Raw) (s : String) : s.Pos :=
  if hValid : offset.IsValid s then ⟨offset, hValid⟩ else s.endPos

def String.editText (file newText : String) (range : Lean.Syntax.Range) : String :=
    file.extract file.startPos (range.start.toPos file)
    ++ newText ++
    file.extract (range.stop.toPos file) file.endPos

def String.highlightCursor (file : String) (cursorPos : String.Pos.Raw) : String :=
  file.editText "∣" ⟨cursorPos, cursorPos⟩

public def testTacticInsertionLogic {M} [Monad M] [MonadLiftT IO M]
    [MonadRef M] [MonadLog M] [AddMessageContext M] [MonadOptions M] [MonadQuotation M]
    (fileContents : String) (cursorPos : Lsp.Position) (tactic : M (TSyntax `tactic))
    (tacticInsertionLogic : TSyntax `tactic → PasteInfo → M Lsp.TextEdit)
    : M Unit := do
  -- Parse the header of the provided file
  let context := Parser.mkInputContext fileContents (fileName := "test.lean")
  let (header, state, messages) ← Parser.parseHeader context
  let text := context.fileMap
  let (environment, messages) ← processHeader header {} messages context
  -- Process the remaining file
  let commandState := { Command.mkState environment messages with infoState := { enabled := true } }
  let s ← IO.processCommands context state commandState
  let trees : List InfoTree := s.commandState.infoState.trees.toList
  let goalsAt := trees.flatMap (·.goalsAt? text (text.lspPosToUtf8Pos cursorPos))
  if h : goalsAt.length = 0 then -- TODO: Use `goalsAt.isEmpty` instead
    IO.throwServerError "No goals found at the given position"
  else
    logInfo <| .trace { cls := `TestTacticInsertion, collapsed := false }
      "Number of goals at result"
      #[m!"{goalsAt.length}"]
    logInfo <| .trace { cls := `TestTacticInsertion } m!"Cursor position"
      #[fileContents.highlightCursor (text.lspPosToUtf8Pos cursorPos)]
    let nearestGoalsAt := goalsAt[0]
    let pasteInfo : PasteInfo := {
      «meta» := { (default : DocumentMeta) with text }
      cursorPos, stx := nearestGoalsAt.tacticInfo.stx }
    let { range, newText, .. } ← tacticInsertionLogic (← tactic) pasteInfo
    let utf8Range := text.lspRangeToUtf8Range range
    logInfo <| .trace { cls := `TestTacticInsertion } m!"Edit details"
      #[m!"Range: {range.start}-{range.end}",
        m!"UTF-8 Range: {utf8Range.start}-{utf8Range.stop}",
        m!"New text: {newText}"]
    let outputFileContents := fileContents.editText newText utf8Range
    logInfo <| .trace { cls := `TestTacticInsertion } m!"Resulting file contents"
      #[outputFileContents.highlightCursor ⟨utf8Range.start.byteIdx + newText.utf8ByteSize⟩]

section Test

def testFile : String :=
"import Lean

open Lean Elab Command Meta Tactic

example : 1 + 1 = 2 := by
  skip
  skip
  "

/--
trace: [TestTacticInsertion] Number of goals at result
  1
---
trace: [TestTacticInsertion] Cursor position
  import Lean
  ⏎
  open Lean Elab Command Meta Tactic
  ⏎
  example : 1 + 1 = 2 := by
    skip
    sk∣ip
    ⏎
---
trace: [TestTacticInsertion] Edit details
  Range: (6, 6)-(6, 6)
  UTF-8 Range: 88-88
  New text: ⏎
    simp
---
trace: [TestTacticInsertion] Resulting file contents
  import Lean
  ⏎
  open Lean Elab Command Meta Tactic
  ⏎
  example : 1 + 1 = 2 := by
    skip
    skip
    simp∣
-/
#guard_msgs in
#eval testTacticInsertionLogic (M := CoreM)
    testFile { line := 6, character := 4 } `(tactic| simp)
    createTacticInsertionEdit



end Test
