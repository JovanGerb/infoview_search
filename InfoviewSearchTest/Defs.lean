module

public import InfoviewSearch
public import ProofWidgets.Component.HtmlDisplay

/-!
# Testing of `#infoview_search`

It is hard to test `#infoview_search` directly, because it emits HTML that the user interacts with.
Instead, we define a (scoped) command `search_test {pos} => "{tac}"`, which verifies that
if you do a `#infoview_search` at position `pos`, `tac` will be one of the suggestions.

TODO: Add way to test preformance.
-/

public meta section

namespace InfoviewSearch.Test
open Lean Meta SubExpr ProofWidgets RefreshComponent Server

def getHtmlComponentProps {Props} [RpcEncodable Props] (html : Html) (c : Component Props)
    (arr : Array Props) : CoreM (Array Props) := do
  match html with
  | .element _ _ htmls => htmls.foldlM (fun arr html ↦ getHtmlComponentProps html c arr) arr
  | .text _ => return arr
  | .component hash _ lazy htmls =>
    let mut arr := arr
    if hash == c.javascriptHash then
      arr := arr.push <| ← getProps lazy
    if hash == FilterDetails.javascriptHash then
      let props : FilterDetailsProps ← getProps lazy
      arr ← getHtmlComponentProps props.all c arr
    if hash == RefreshComponent.javascriptHash then
      let props : RefreshComponentProps ← getProps lazy
      arr ← getHtmlComponentProps (← props.state.val.get).curr.html c arr
    htmls.foldlM (fun arr html ↦ getHtmlComponentProps html c arr) arr
where
  getProps {Props} [RpcEncodable Props] (lazy : LazyEncodable Json) :
      CoreM Props := do
    let (json, state) := lazy.run {}
    match rpcDecode json state with
    | .ok props => return props
    | .error s => throwError "An error occurred when looking at the HTML: {s}"

scoped elab "search_test" hyp?:(ident)? pos?:(str)? "=>" expecteds:str+ : tactic =>
  Elab.Tactic.withMainContext do
  let hyp? ← hyp?.mapM fun hyp ↦ return (← getLocalDeclFromUserName hyp.getId).fvarId
  let pos? ← pos?.mapM fun pos ↦ do
    match Pos.fromString? pos.getString with
    | .ok pos => return pos
    | .error s => throwError "{s}"
  let expecteds := expecteds.map (·.getString)
  let loc : GoalLocation := ← match hyp?, pos? with
    | some h, some pos => pure <| .hypType h pos
    | none  , some pos => pure <| .target pos
    | some h, none     => pure <| .hyp h
    | _     , _        => throwError "please provide a position"
  let mvarId ← Elab.Tactic.getMainGoal
  let text ← getFileMap
  let some cursorPos := (← getRef).getPos? | throwError "found no valid cursor position"
  let cursorPos := text.utf8PosToLspPos cursorPos
  let pasteInfo := {
    «meta» := { (default : DocumentMeta) with text }, cursorPos, onGoal := none, stx := default }
  let token ← RefreshToken.new default
  generateSuggestions { loc, mvarId } pasteInfo none token
  let html := (← token.ref.get).curr.html
  let props ← getHtmlComponentProps html MakeEditLink #[]
  let suggested := props.flatMap (·.edit.edits.map (·.newText))
  for expected in expecteds do
    unless suggested.contains expected do
      throwError "{expected.quote} is not one of the suggestions: {suggested.map (·.quote)}"

end InfoviewSearch.Test
