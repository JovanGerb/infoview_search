/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import ProofWidgets.Component.Panel.Basic
public import ProofWidgets.Data.Html
public import InfoviewSearch.ForUpstream

/-!
# The `RefreshComponent` widget

This file defines `RefreshComponent`, which allows you to have an HTML widget that updates
incrementally as more results are computed by a Lean computation.

For this interaction, we use an `IO.Ref` that the JavaScript reads from.
It stores the HTML that should currently be on display, and a task returning the next HTML.
To determine whether the widget is up to date, each computed HTML has an associated version number.
(So, the `n`-th HTML will have index `n`)

When the widget (re)loads, it first loads the current HTML from the ref, and then
repeatedly awaits further HTML result.

## Known limitations

Cancellation is a bit hard to get right, and there are two limitations.

1. When using a `RefreshComponent` that reacts to shift-clicking in the infoview,
we want to cancel the computation whenever a new selection is made.
We acomplish this in `mkCancelPanelWidget` by creating a reference to a cancel token,
which we can reset every time a new selection is made.
On the other hand, we would also like to cancel the computation if that part of the file gets
reloaded. Unfortunately, the `CoreM` monad can only store up to 1 cancel token at a time.
The result is that if you close the infoview while the widget is active, and then reload
this part of the file, the widget computation keeps running without any way to stop it
(except for restarting the file, or waiting it out)
2. When using a `RefreshComponent` that comes directly from a command/tactic (no shift-clicking),
then we pass the cancel token used by elaboration to the refresh component computation.
Unfortunately there is an edge case where the cancel token gets set while the corresponding
command does not get re-elaborated. In particular, if you have three command in a row, e.g.
```
#html countToTen
#html countToTen
#html countToTen
```
Then commenting out the third command will cancel the widget of the first command.
It refreshes the second command, and doesn't affect commands before the first command - only
the first command gets badly affected.
-/


public meta section

namespace ProofWidgets
open Lean Server Widget Jsx
namespace RefreshComponent

/-- The result that is sent to the `RefreshComponent` after each query. -/
structure Versioned (α : Type) where
  /-- The new HTML that will replace the current HTML. -/
  val : α
  /-- The version number of the HTML. It is a count of how many HTMLs were created. -/
  idx : Nat
  deriving RpcEncodable, Nonempty

@[inline]
def Versioned.map {α β : Type} (f : α → β) (v : Versioned α) : Versioned β where
  val := f v.val
  idx := v.idx

/-- The `RefreshState` stores the incremental result of the HTML computation. -/
private structure RefreshState (σ : Type) where
  /-- The state that the widget should currently be in. -/
  curr : Versioned σ
  /-- A task that returns the next state for the widget.
  It is always implemented using `IO.Promise.result?`. -/
  next : Task (Option (Versioned σ))
  deriving Nonempty

structure RefreshInfo (σ : Type) where
  private ref : IO.Ref (RefreshState σ)
  private decode : σ → Html
  deriving Nonempty

/-- Wait until the state has finished refreshing, and the return the final HTML.
This is useful for inspecting `Html` from within Lean. -/
partial def RefreshInfo.getFinalHtml (info : RefreshInfo σ) : BaseIO Html := do
  let { curr, next } ← info.ref.get
  if next.get.isNone then
    return info.decode curr.val
  info.getFinalHtml

section RPC

private opaque OpaqueStateImpl : NonemptyType.{0}
def OpaqueState : Type := OpaqueStateImpl.type
private instance : Nonempty OpaqueState := by exact OpaqueStateImpl.property

/-- A reference to a `RefreshState`. This is used to keep track of the refresh state. -/
abbrev OpaqueRefreshInfo := RefreshInfo OpaqueState

instance : TypeName OpaqueRefreshInfo := unsafe .mk OpaqueRefreshInfo ``OpaqueRefreshInfo

/-- The data used to call `awaitRefresh`, for updating the HTML display. -/
structure AwaitRefreshParams where
  /-- The reference to the `RefreshState`. -/
  state : WithRpcRef OpaqueRefreshInfo
  /-- The index of the HTML that is currently on display. -/
  oldIdx : Nat
  deriving RpcEncodable


/-- `awaitRefresh` is called through RPC to obtain the next HTML to display. -/
@[server_rpc_method]
def awaitRefresh (props : AwaitRefreshParams) : RequestM (RequestTask (Option (Versioned Html))) := do
  let { ref, decode } := props.state.val
  let { curr, next } ← ref.get
  -- If `props.oldIdx < curr.idx`, that means that the state has updated in the meantime.
  -- So, returning `curr` will give a refresh.
  -- If `props.oldIdx = curr.idx`, then we need to await `next` to get a refresh
  if props.oldIdx != curr.idx then
    return .pure (curr.map decode)
  else
    return .mapCostly (.ok <| ·.map (·.map decode)) ⟨next⟩

/--
`getCurrState` is called through RPC whenever the widget reloads.
This can be because the infoview was closed and reopened,
or because a different expression was selected in the goal.
-/
@[server_rpc_method]
def getCurrState (ref : WithRpcRef OpaqueRefreshInfo) : RequestM (RequestTask (Versioned Html)) :=
  RequestM.asTask do
    let { ref, decode } := ref.val
    return (← ref.get).curr.map decode

end RPC

end RefreshComponent

open RefreshComponent

/-- The argument passed to `RefreshComponent`. -/
structure RefreshComponentProps where
  /-- The refresh state that is queried for updating the display. -/
  state : WithRpcRef OpaqueRefreshInfo
  deriving RpcEncodable

/-- Display an inital HTML, and repeatedly update the display with new HTML objects
as they appear in `state`. A dedicated thread should be spawned in order to modify `state`. -/
@[widget_module]
def RefreshComponent : Component RefreshComponentProps where
  javascript := "window;import{jsxs as e,jsx as t,Fragment as n}from\"react/jsx-runtime\";import*as r from\"react\";import a from\"react\";import{useRpcSession as o,EnvPosContext as i,useAsyncPersistent as s,mapRpcError as c,importWidgetModule as l}from\"@leanprover/infoview\";async function m(a,o,i){if(\"text\"in i)return t(n,{children:i.text});if(\"element\"in i){const[e,n,s]=i.element,c={};for(const[e,t]of n)c[e]=t;const l=await Promise.all(s.map((async e=>await m(a,o,e))));return\"hr\"===e?t(\"hr\",{}):0===l.length?r.createElement(e,c):r.createElement(e,c,l)}if(\"component\"in i){const[e,t,n,s]=i.component,c=await Promise.all(s.map((async e=>await m(a,o,e)))),f={...n,pos:o},u=await l(a,o,e);if(!(t in u))throw new Error(`Module '${e}' does not export '${t}'`);return 0===c.length?r.createElement(u[t],f):r.createElement(u[t],f,c)}return e(\"span\",{className:\"red\",children:[\"Unknown HTML variant: \",JSON.stringify(i)]})}function f({val:a}){const l=o(),f=r.useContext(i),u=s((()=>m(l,f,a)),[l,f,a]);return\"resolved\"===u.state?u.value:\"rejected\"===u.state?e(\"span\",{className:\"red\",children:[\"Error rendering HTML: \",c(u.error).message]}):t(n,{})}function u(e){const r=o(),[i,s]=a.useState(null);return a.useEffect((()=>{let t=!1;async function n(a){const o=await r.call(\"ProofWidgets.RefreshComponent.awaitRefresh\",{oldIdx:a,state:e.state});if(!t&&o)return s(o.val),n(o.idx)}return(async()=>{const a=await r.call(\"ProofWidgets.RefreshComponent.getCurrState\",e.state);if(!t)s(a.val),n(a.idx)})(),()=>{t=!0}}),[e]),i?t(f,{val:i}):t(n,{})}export{u as default};"


/-! ## API for creating a `RefreshComponent` -/

/-- A `RefreshToken` allows you to update the state of the corresponding `RefreshComponent`. -/
structure RefreshToken (σ : Type) where
  /-- The reference that was given to the corresponding `RefreshComponent`. -/
  private refreshRef : IO.Ref (RefreshState σ)
  /-- The promise that will resolve the `next` field in `ref`.
  If we drop the reference to this structure, and hence to this promise,
  the `next` field will resolve to `none`. -/
  private promise : IO.Ref (IO.Promise (Versioned σ))

variable {σ} [Nonempty σ]

/-- Create a fresh `RefreshToken` with initial HTML `initial`. -/
private def RefreshToken.new (initial : σ) : BaseIO (RefreshToken σ) := do
  let promise ← IO.Promise.new
  return {
    refreshRef := ← IO.mkRef {
      curr := { val := initial, idx := 0 }
      next := promise.result? }
    promise := ← IO.mkRef promise }

/-- Return the current state from the `RefreshToken`-/
def RefreshToken.getCurrState (token : RefreshToken σ) : BaseIO σ  := do
  return (← token.refreshRef.get).curr.val

/-- Update the current HTML to be `html`.
This function makes use of `ST.Ref.take` in order to be thread safe.
That is, if multiple different threads call this function with the same refresh token,
a call will block other calls until it is finished. -/
@[specialize]
def RefreshToken.modifyM (token : RefreshToken σ)
    (f : σ → BaseIO σ) : BaseIO Unit := unsafe do
  let { refreshRef, promise } := token
  let { val, idx } := (← refreshRef.take).curr
  let next := {
    val := ← f val
    idx := idx + 1 }
  (← promise.get).resolve next
  let newPromise ← IO.Promise.new
  promise.set newPromise
  refreshRef.set { curr := next, next := newPromise.result? }

@[specialize]
def RefreshToken.modify (token : RefreshToken σ) (f : σ → σ) : BaseIO Unit :=
  token.modifyM fun s ↦ return (f s)

def RefreshToken.set (token : RefreshToken σ) (val : σ) : BaseIO Unit :=
  token.modifyM fun _ ↦ return val

/-- Create an HTML, together with a `RefreshToken` that can be used to update this HTML. -/
def mkRefreshComponent (initial : σ) (decode : σ → Html) : BaseIO (Html × RefreshToken σ) := do
  let token ← RefreshToken.new initial
  let info : RefreshInfo σ := { ref := token.refreshRef, decode }
  let info : RefreshInfo OpaqueState := unsafe unsafeCast info
  return (<RefreshComponent state={← WithRpcRef.mk info}/>, token)

variable {m} [Monad m] [MonadDrop m (EIO Exception)] [MonadLiftT BaseIO m]

/-- Create a `RefreshComponent` using the computation `k`.
In order to implicitly support cancellation, `m` should extend `CoreM`,
and hence have access to a cancel token. -/
def mkRefreshComponentM (initial : Html) (k : RefreshToken Html → m Unit) : m Html := do
  let (html, token) ← mkRefreshComponent initial id
  discard <| BaseIO.asTask (prio := .dedicated) <|
    (← dropM <| k token).catchExceptions fun ex => token.set =<< do
      if let .internal id _ := ex then
        if id == interruptExceptionId then
          return .text "This component was cancelled"
      return <span>
          An error occurred while refreshing this component:
          <InteractiveMessage msg={← WithRpcRef.mk ex.toMessageData}/>
        </span>
  return html

/-- Lazily render a piece of HTML by running the computation in a separate thread.
As long as the computation hasn't finished, the result will show up as `initial`. -/
def mkLazyHtml (k : m (Option Html)) (initial : Html := .text "") : m Html := do
  mkRefreshComponentM initial (do if let some html ← k then ·.set html)

abbrev CancelTokenRef := IO.Ref IO.CancelToken

instance : TypeName CancelTokenRef := unsafe .mk CancelTokenRef ``CancelTokenRef

/-- `CancelPanelWidgetProps` are the arguments passed to a widget which supports cancellation. -/
structure CancelPanelWidgetProps extends PanelWidgetProps where
  /-- `cancelTkRef` is a reference to the cancel token of the most recent instance of the widget. -/
  cancelTkRef : WithRpcRef (IO.Ref IO.CancelToken)
  deriving RpcEncodable

/-- Return a widget that supports cancellation via `CancelPanelWidgetProps`.
The widget can be activated with for example `addPanelWidgetLocal` or  `addPanelWidgetGlobal`. -/
def mkCancelPanelWidget (component : Component CancelPanelWidgetProps) : CoreM WidgetInstance := do
  let cancelTkRef ← WithRpcRef.mk (← IO.mkRef (← IO.CancelToken.new))
  Widget.WidgetInstance.ofHash component.javascriptHash
    (return json% {cancelTkRef : $(← rpcEncode cancelTkRef)})

end ProofWidgets
