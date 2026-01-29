module

public import Lean
public import InfoviewSearch.Util

open Lean Elab Command Meta Tactic Server InfoviewSearch

deriving instance Repr for ElabInfo

public meta def testTacticInsertionLogic {M}
    [Monad M] [MonadLiftT IO M] [MonadRef M] [MonadQuotation M]
    (fileContents : String) (cursorPos : Lsp.Position)
    (tactic : TSyntax `tactic) (expectedOutput : String)
    (tacticInsertionLogic : TSyntax `tactic → PasteInfo → M Lsp.TextEdit) : M Bool := do
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
    IO.println goalsAt.length
    let nearestGoalsAt := goalsAt[0]
    let pasteInfo : PasteInfo := {
      «meta» := { (default : DocumentMeta) with text }
      cursorPos, stx := nearestGoalsAt.tacticInfo.stx }
    let { range, newText, .. } ← tacticInsertionLogic tactic pasteInfo
    return editText fileContents (text.lspRangeToUtf8Range range) newText == expectedOutput
where
  editText (file : String) (range : Lean.Syntax.Range) (newText : String) : String :=
    let startPos : file.Pos :=
      if hValid : range.start.IsValid file then ⟨range.start, hValid⟩ else file.endPos
    let endPos : file.Pos :=
      if hValid : range.stop.IsValid file then ⟨range.stop, hValid⟩ else file.endPos
    file.extract file.startPos startPos ++ newText ++ file.extract endPos file.endPos

private def testFile : String :=
"import Lean

open Lean Elab Command Meta Tactic

example : 1 + 1 = 2 := by
  skip
  skip
  "

private def testFile.expectedOutput : String :=
"import Lean

open Lean Elab Command Meta Tactic

example : 1 + 1 = 2 := by
  skip
  skip
  simp
  "

#eval show CoreM _ from do
  testTacticInsertionLogic
    testFile { line := 7, character := 6 }
    (← `(tactic| simp))
    testFile.expectedOutput
    createTacticInsertionEdit
