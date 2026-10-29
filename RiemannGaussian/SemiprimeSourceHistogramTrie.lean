/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceCompactBits

/-! # Deterministic paid Boolean-key frequency trie
Terminal values are optional compact physical counter words. Empty and prefix keys
are distinct. Sibling/reference reuse is explicit persistent-node bookkeeping,
not a complete pointer/tape representation theorem.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramTrie
open SemiprimeBitArithmetic
open SemiprimeSourceCompactBits (Compact)

/-- Physical Boolean-key trie, with a separate counter at each terminal position. -/
inductive Trie where
  /-- No terminal or child nodes have been acquired. -/
  | empty
  /-- Optional frequency payload and false/true children. -/
  | node (payload : Option (List Bool)) (falseChild trueChild : Trie)
  deriving Repr

/-- Constant-field terminal lookup; no semantic count interpretation is executed. -/
def payload : Trie → Option (List Bool)
  | .empty => none
  | .node v _ _ => v

/-- Actual one-bit branch selection. -/
def child : Trie → Bool → Trie
  | .empty,_ => .empty
  | .node _ l _,false => l
  | .node _ _ r,true => r

/-- Replace one actual branch while retaining the untouched immutable sibling. -/
def replace (t : Trie) (b : Bool) (next : Trie) : Trie :=
  .node (payload t) (if b then child t false else next) (if b then next else child t true)

/-- Proof-side physical payload at a key, absent keys denoting literal empty zero. -/
def stored (t : Trie) : List Bool → List Bool
  | [] => (payload t).getD []
  | b::bs => stored (child t b) bs

/-- Mathematical frequency specification, never called to execute trie operations. -/
def value (t : Trie) (key : List Bool) : ℕ := bitValue (stored t key)

/-- Physical lookup copies only the actual selected terminal counter. -/
def lookup : Trie → List Bool → SemiprimeSourceCompactBits.Report
  | .empty,_ => ⟨[],2⟩
  | .node v _ _,[] =>
    let out := SemiprimeSourceCompactBits.copy (v.getD [])
    ⟨out.bits,out.clock+8⟩
  | .node _ l r,b::bs =>
    let out := lookup (if b then r else l) bs
    ⟨out.bits,out.clock+8⟩

/-- Single-path update returns a physically copied OLD frequency and the new trie. -/
structure Bump where
  /-- Exact old counter bits, physically copied once at the selected terminal. -/
  old : List Bool
  /-- Actual updated persistent trie. -/
  trie : Trie
  /-- Every visited key/node, terminal copy and compact increment report. -/
  clock : ℕ

/-- One actual key-path traversal; no second lookup or integer-count oracle. -/
def bump (t : Trie) : List Bool → Bump
  | [] =>
    let old := (payload t).getD []
    let copied := SemiprimeSourceCompactBits.copy old
    let next := SemiprimeSourceCompactBits.increment old
    ⟨copied.bits,.node (some next.bits) (child t false) (child t true),copied.clock+next.clock+20⟩
  | b::bs =>
    let out := bump (child t b) bs
    ⟨out.old,replace t b out.trie,out.clock+20⟩

/-- Empty trie defaults are literal zero for all keys. -/
theorem stored_empty (key : List Bool) : stored .empty key=[] := by
  induction key with
  | nil => rfl
  | cons b bs ih => simpa only [stored,child] using ih

/-- Physical lookups preserve exact stored payload bits. -/
theorem lookup_bits (t : Trie) (key : List Bool) : (lookup t key).bits=stored t key := by
  induction key generalizing t with
  | nil => cases t <;> simp [lookup,stored,payload,SemiprimeSourceCompactBits.copy_bits]
  | cons b bs ih =>
    cases t with
    | empty => simp [lookup,stored_empty]
    | node v l r => cases b <;> simp [lookup,stored,child,ih]

/-- Numeric lookup is exact, including absent and prefix keys. -/
theorem lookup_value (t : Trie) (key : List Bool) : bitValue (lookup t key).bits=value t key := by
  rw [lookup_bits]
  rfl

/-- Bump returns the exact old physical payload from the same traversal. -/
theorem bump_old (t : Trie) (key : List Bool) : (bump t key).old=stored t key := by
  induction key generalizing t with
  | nil => simp only [bump,stored,SemiprimeSourceCompactBits.copy_bits]
  | cons b bs ih => exact ih (child t b)

/-- Exact changed-key payload and preservation of every other key, including prefixes. -/
theorem bump_stored (t : Trie) (key query : List Bool) :
    stored (bump t key).trie query=
      if query=key then (SemiprimeSourceCompactBits.increment (stored t key)).bits else stored t query := by
  induction key generalizing t query with
  | nil =>
    cases query with
    | nil => rfl
    | cons b bs => cases t <;> cases b <;> simp [bump,stored,child,payload]
  | cons b bs ih =>
    cases query with
    | nil => simp [bump,stored,replace,payload]
    | cons c cs =>
      cases b <;> cases c <;> simp [bump,stored,replace,child,ih]

/-- Actual updated frequency, with no advised stored count or encoded answer. -/
theorem bump_value (t : Trie) (key query : List Bool) :
    value (bump t key).trie query=if query=key then value t query+1 else value t query := by
  unfold value
  rw [bump_stored]
  split_ifs with h
  · subst query
    exact SemiprimeSourceCompactBits.increment_value _
  · rfl

/-- Empty/default and prefix-terminal updates are included in exact same-key increment. -/
theorem bump_same (t : Trie) (key : List Bool) : value (bump t key).trie key=value t key+1 := by
  simp only [bump_value,ite_true]

/-- A distinct key's frequency is unchanged. -/
theorem bump_other (t : Trie) (key query : List Bool) (h : query≠key) :
    value (bump t key).trie query=value t query := by simp only [bump_value,h,ite_false]

/-- Logical persistent-node inventory; duplicate references are conservatively counted. -/
def nodes : Trie → ℕ
  | .empty => 0
  | .node _ l r => 1+nodes l+nodes r

/-- Only one key path allocates nodes; no unvisited subtree is rebuilt. -/
theorem bump_nodes (t : Trie) (key : List Bool) :
    nodes (bump t key).trie ≤ nodes t+key.length+1 := by
  induction key generalizing t with
  | nil => cases t <;> simp [bump,nodes,child,payload]
  | cons b bs ih =>
    have h := ih (child t b)
    cases t <;> cases b <;> simp only [bump,replace,nodes,child,payload,List.length_cons,
      Bool.false_eq_true,ite_false,ite_true] at h ⊢ <;> omega

/-- Canonical counters at every stored terminal, absent positions included. -/
def CompactCounters (t : Trie) : Prop := ∀ key,Compact (stored t key)

/-- Empty original dictionary has compact zero everywhere. -/
theorem empty_compact : CompactCounters .empty := by intro key;rw [stored_empty];trivial

/-- Every actual update preserves canonical frequency counters. -/
theorem bump_compact (t : Trie) (key : List Bool) (ht : CompactCounters t) :
    CompactCounters (bump t key).trie := by
  intro query
  rw [bump_stored]
  split_ifs
  · exact SemiprimeSourceCompactBits.increment_compact _
  · exact ht query

end RiemannGaussian.SemiprimeSourceHistogramTrie
