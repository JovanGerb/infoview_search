/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup
public import InfoviewSearch.ForUpstream

/-!
# Matching with a RefinedDiscrTree

This file defines the matching procedure for the `RefinedDiscrTree`.

The main definitions are
* The structure `MatchResult`, which contains the match results, ordered by matching score.
* The (private) function `evalNode` which evaluates a node of the `RefinedDiscrTree`
* The (private) function `getMatchLoop`, which is the main function that computes the matches.
  It implements the non-deterministic computation by keeping a stack of `PartialMatch`es,
  and repeatedly processing the most recent one.
* The matching function `getMatch` that also returns an updated `RefinedDiscrTree`

To find the matches, we first encode the expression as a `List Key`. Then using this,
we find all matches with the tree. When `unify == true`, we also allow metavariables in the target
expression to be assigned.

We use a simple unification algorithm. For all star/metavariable patterns in the
`RefinedDiscrTree` (and in the target if `unify == true`), we store the assignment,
and when it is attempted to be assigned again, we check that it is the same assignment.

-/

namespace Lean.Meta.RefinedDiscrTree

variable {α β : Type}

/-- Monad for working with a `RefinedDiscrTree`. -/
abbrev TreeM α := StateRefT (Array (Trie α)) MetaM

/-- Create a new trie with the given lazy entry. -/
def newTrie (e : LazyEntry × α) : TreeM α TrieIndex := do
  modifyGet fun a => (a.size, a.push (.node #[] none {} {} #[e]))

/-- Add a lazy entry to an existing trie. -/
def addLazyEntryToTrie (i : TrieIndex) (e : LazyEntry × α) : TreeM α Unit :=
  modify (·.modify i fun node => { node with pending := node.pending.push e })

/-- Process a specified range of pending entries. -/
def processPendingRange (pending : Array (LazyEntry × α)) (start stop : Nat) :
    MetaM (Array α × Array (Key × LazyEntry × α)) :=
  pending.foldlM (start := start) (stop := stop) (init := (#[], #[]))
    fun (values, pending) (entry, value) ↦ do
    if let some newEntries ← evalLazyEntry entry true then
      return (values, newEntries.foldl (init := pending) fun pending (key, entry) ↦
        pending.push (key, entry, value))
    else
      return (values.push value, pending)

/--
Evaluate the `Trie α` at index `trie`,
replacing it with the evaluated value,
and returning the `Trie α`.

Performance note: In the `apply` search discrimination tree, after root node `⟨Eq, 3⟩`,
there are around `150.000` entries in the `pending` array.
To deal with this smoothly, we use paralellism.
-/
def evalNode (trie : TrieIndex) : TreeM α (Trie α) := do
  let node := (← get)[trie]!
  if node.pending.isEmpty then
    return node
  let numTasks := node.pending.size / 5000 + 1
  let tasks ← numTasks.foldM (init := #[]) fun i _ tasks ↦ do
    return tasks.push <| ← BaseIO.asTask <| (← dropM do
      processPendingRange node.pending (i * 5000) ((i + 1) * 5000)).catchExceptions fun ex ↦ do
        if let .internal id _ := ex then
          if id == interruptExceptionId then
            return (#[], #[])
        panic! "error while processing the discrimination tree: {← ex.toMessageData.toString}"
  Core.checkInterrupted
  modify (·.set! trie default) -- reduce the reference count to `node` to be 1
  let mut { values, star, labelledStars, children, .. } := node
  for task in tasks do
    let (values', pending) := task.get
    values := values ++ values'
    for (key, entry) in pending do
      match key with
      | .labelledStar label =>
        if let some trie := labelledStars[label]? then
          addLazyEntryToTrie trie entry
        else
          labelledStars := labelledStars.insert label (← newTrie entry)
      | .star =>
        if let some trie := star then
          addLazyEntryToTrie trie entry
        else
          star := some (← newTrie entry)
      | _ =>
        if let some trie := children[key]? then
          addLazyEntryToTrie trie entry
        else
          children := children.insert key (← newTrie entry)
  let node := { values, star, labelledStars, children, pending := #[] }
  modify (·.set! trie node)
  return node

def MatchResult.push (mr : MatchResult α) (score : Nat) (e : Array α) : MatchResult α :=
  { elts := mr.elts.alter score fun | some arr => arr.push e | none => #[e] }

/-
A partial match captures the intermediate state of a match execution.

N.B. Discrimination tree matching has non-determinism due to stars,
so the matching loop maintains a stack of partial match results.
-/
structure PartialMatch where
  /-- Remaining terms to match -/
  keys : List Key
  /-- Number of non-star matches so far -/
  score : Nat
  /-- Trie to match next -/
  trie : TrieIndex
  /-- Metavariable assignments for `.labelledStar` patterns in the discrimination tree.
  We use a `List Key`, in the reverse order. -/
  treeStars : Std.HashMap Nat (List Key) := {}
  deriving Inhabited


/--
Add to the `todo` stack all matches that result from a `.star` in the query expression.
-/
partial def matchQueryStar (trie : TrieIndex) (pMatch : PartialMatch)
    (todo : Array PartialMatch) (skip : Nat := 1) : TreeM α (Array PartialMatch) := do
  match skip with
  | skip+1 =>
    let { star, labelledStars, children, .. } ← evalNode trie
    let mut todo := todo
    if let some trie := star then
      todo ← matchQueryStar trie pMatch todo skip
    todo ← labelledStars.foldM (init := todo) fun todo _ trie =>
      matchQueryStar trie pMatch todo skip
    todo ← children.foldM (init := todo) fun todo key trie =>
      matchQueryStar trie pMatch todo (skip + key.arity)
    return todo
  | 0 =>
    return todo.push { pMatch with trie }

/-- Return every value that is indexed in the tree. -/
def matchEverything (root : Std.HashMap Key TrieIndex) : TreeM α (MatchResult α) := do
  let pMatches ← root.foldM (init := #[]) fun todo key trie =>
    matchQueryStar trie { keys := [], score := 0, trie := 0 } todo key.arity
  pMatches.foldlM (init := {}) fun result pMatch => do
    let { values, .. } ← evalNode pMatch.trie
    return result.push (score := 0) values

/-- Add to the `todo` stack all matches that result from a `.star _` in the discrimination tree. -/
partial def matchTreeStars (key : Key) (node : Trie α) (pMatch : PartialMatch)
    (todo : Array PartialMatch) (unify : Bool) : Array PartialMatch := Id.run do
  let { star, labelledStars, .. } := node
  if labelledStars.isEmpty && star.isNone then
    todo
  else
    let (dropped, keys) := drop [key] pMatch.keys key.arity
    let mut todo := todo
    if let some trie := star then
      todo := todo.push { pMatch with keys, trie }
    todo := node.labelledStars.fold (init := todo) fun todo id trie =>
      if let some assignment := pMatch.treeStars[id]? then
        let eq lhs rhs := if unify then (isEq lhs.reverse rhs.reverse).isSome else lhs == rhs
        if eq dropped assignment then
          todo.push { pMatch with keys, trie, score := pMatch.score + dropped.length }
        else
          todo
      else
        let treeStars := pMatch.treeStars.insert id dropped
        todo.push { pMatch with keys, trie, treeStars }
    return todo
where
  /-- Drop the keys corresponding to the next `n` expressions. -/
  drop (dropped rest : List Key) (n : Nat) : (List Key × List Key) := Id.run do
    match n with
    | 0 => (dropped, rest)
    | n + 1 =>
      let key :: rest := rest | panic! "too few keys"
      drop (key :: dropped) rest (n + key.arity)
  isEq (lhs rhs : List Key) : Option (List Key × List Key) := do
    match lhs with
    | [] => panic! "too few keys"
    | .star :: lhs =>
      let (_, rhs) := drop [] rhs 1
      return (lhs, rhs)
    | lHead :: lhs =>
    match rhs with
    | [] => panic! "too few keys"
    | .star :: rhs =>
      let (_, lhs) := drop [] lhs 1
      return (lhs, rhs)
    | rHead :: rhs =>
      guard (lHead == rHead)
      lHead.arity.foldM (init := (lhs, rhs)) fun _ _ (lhs, rhs) => isEq lhs rhs

/-- Add to the `todo` stack the match with `key`. -/
def matchKey (key : Key) (children : Std.HashMap Key TrieIndex) (pMatch : PartialMatch)
    (todo : Array PartialMatch) : Array PartialMatch :=
  if key == .opaque then todo else
  match children[key]? with
  | none      => todo
  | some trie => todo.push { pMatch with trie, score := pMatch.score + 1 }

/-- Return the possible `Trie α` that match with `keys`. -/
partial def getMatchLoop (todo : Array PartialMatch) (result : MatchResult α)
    (unify : Bool) : TreeM α (MatchResult α) := do
  if h : todo.size = 0 then
    return result
  else
    let pMatch := todo.back
    let todo := todo.pop
    let node ← evalNode pMatch.trie
    match pMatch.keys with
    | [] =>
      getMatchLoop todo (result.push (score := pMatch.score) node.values) unify
    | key :: keys =>
      let pMatch := { pMatch with keys }
      match key with
      -- `key` is not a `.labelledStar`
      | .star =>
        if unify then
          let todo ← matchQueryStar pMatch.trie pMatch todo
          getMatchLoop todo result unify
        else
          let todo := matchTreeStars key node pMatch todo unify
          getMatchLoop todo result unify
      | _ =>
        let todo := matchTreeStars key node pMatch todo unify
        let todo := matchKey key node.children pMatch todo
        getMatchLoop todo result unify

/-- Return the results from matching the pattern `[.star]` or `[.labelledStar 0]`. -/
def matchTreeRootStar (root : Std.HashMap Key TrieIndex) : TreeM α (MatchResult α) := do
  let mut result := {}
  if let some trie := root[Key.labelledStar 0]? then
    let { values, .. } ← evalNode trie
    result := result.push (score := 0) values
  if let some trie := root[Key.star]? then
    let { values, .. } ← evalNode trie
    result := result.push (score := 0) values
  return result

/--
Find values that match `e` in `d`.
* If `unify == true` then metavariables in `e` can be assigned.
* If `matchRootStar == true` then we allow metavariables at the root to unify.
  Set this to `false` to avoid getting excessively many results.

Note: to preserve the reference to `d`, `getMatch` will never throw an error,
and instead it returns an `Except Exception (MatchResult α)`.
-/
def getMatchAux (root : Std.HashMap Key TrieIndex) (e : Expr) (unify matchRootStar : Bool) :
    TreeM α (MatchResult α) := do
  withReducible do
    let (key, keys) ← encodeExpr e (labelledStars := false)
    let pMatch : PartialMatch := { keys, score := 0, trie := default }
    if key == .star then
      if matchRootStar then
        if unify then
          matchEverything root
        else
          matchTreeRootStar root
      else
        return {}
    else
      let todo := matchKey key root pMatch #[]
      if matchRootStar then
        getMatchLoop todo (← matchTreeRootStar root) unify
      else
        getMatchLoop todo {} unify

-- Avoid name collision with the `getMatch` from mathlib.
public def getMatchTemp (d : RefinedDiscrTree α) (e : Expr) (unify matchRootStar : Bool) :
    MetaM (MatchResult α × RefinedDiscrTree α) := do
  -- Make sure that heartbeats don't limit us here.
  withTheReader Core.Context ({ · with maxHeartbeats := 0 }) do
  let (result, tries) ← (getMatchAux d.root e unify matchRootStar).run d.tries
  return (result, { d with tries })

end Lean.Meta.RefinedDiscrTree
