/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramTrieBounds

/-! # Paid raw physical-payload insertion into the deterministic trie
Selected original IDs/encoded rows are copied as exact bytes, without trimming.
Source constructors provide those actual payloads; no desired lookup answer is
an input to a final source endpoint. Reference/tape lowering remains separate.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramTrieStore
open SemiprimeSourceHistogramTrie SemiprimeBitArithmetic
open SemiprimeSourceCompactBits (Compact)

/-- Actual raw-value insertion report. -/
structure Put where
  /-- New persistent map with the one selected key changed. -/
  trie : Trie
  /-- Every visited key/node, payload copy and node-constructor stage. -/
  clock : ℕ

/-- One actual key path and one physical terminal-payload copy. -/
def put (t : Trie) : List Bool → List Bool → Put
  | [],data =>
    let out := SemiprimeSourceCompactBits.copy data
    ⟨.node (some out.bits) (child t false) (child t true),out.clock+20⟩
  | b::bs,data =>
    let out := put (child t b) bs data
    ⟨replace t b out.trie,out.clock+20⟩

/-- Exact byte semantics includes absent, empty and prefix keys. -/
theorem put_stored (t : Trie) (key data query : List Bool) :
    stored (put t key data).trie query=if query=key then data else stored t query := by
  induction key generalizing t query with
  | nil =>
    cases query with
    | nil => simp only [put,stored,payload,SemiprimeSourceCompactBits.copy_bits,ite_true,Option.getD_some]
    | cons b bs => cases t <;> cases b <;> simp [put,stored,child]
  | cons b bs ih =>
    cases query with
    | nil => simp [put,stored,replace,payload]
    | cons c cs => cases b <;> cases c <;> simp [put,stored,replace,child,ih]

/-- The executed physical lookup returns exactly the inserted bytes at that key. -/
theorem put_lookup (t : Trie) (key data query : List Bool) :
    (lookup (put t key data).trie query).bits=
      if query=key then data else (lookup t query).bits := by
  rw [lookup_bits,put_stored,lookup_bits]

/-- Selected-key exact bytes, not only their numeric interpretation. -/
theorem put_same (t : Trie) (key data : List Bool) :
    (lookup (put t key data).trie key).bits=data := by simp only [put_lookup,ite_true]

/-- Every distinct key, including strict prefixes/extensions, retains its exact bytes. -/
theorem put_other (t : Trie) (key data query : List Bool) (h : query≠key) :
    (lookup (put t key data).trie query).bits=(lookup t query).bits := by simp only [put_lookup,h,ite_false]

/-- Numeric interpretation is a corollary, never an executed insertion oracle. -/
theorem put_value (t : Trie) (key data query : List Bool) :
    value (put t key data).trie query=if query=key then bitValue data else value t query := by
  unfold value
  rw [put_stored]
  split_ifs <;> rfl

/-- Only one path acquires new nodes; untouched subtrees are not traversed or copied. -/
theorem put_nodes (t : Trie) (key data : List Bool) :
    nodes (put t key data).trie ≤ nodes t+key.length+1 := by
  induction key generalizing t with
  | nil => cases t <;> simp [put,nodes,child]
  | cons b bs ih =>
    have h := ih (child t b)
    cases t <;> cases b <;> simp only [put,replace,nodes,child,payload,List.length_cons,
      Bool.false_eq_true,ite_false,ite_true] at h ⊢ <;> omega

/-- Compact counters remain compact when actual compact payloads are inserted. -/
theorem put_compact (t : Trie) (key data : List Bool) (ht : CompactCounters t) (hd : Compact data) :
    CompactCounters (put t key data).trie := by
  intro query
  rw [put_stored]
  split_ifs
  · exact hd
  · exact ht query

/-- All raw original payload widths propagate without a count/value/Fits assumption. -/
theorem put_width (t : Trie) (key data : List Bool) (B : ℕ)
    (ht : ∀ query,(stored t query).length ≤ B) (hd : data.length ≤ B) :
    ∀ query,(stored (put t key data).trie query).length ≤ B := by
  intro query
  rw [put_stored]
  split_ifs
  · exact hd
  · exact ht query

/-- Exact retained clock identifies the one terminal copy and every key-frame stage. -/
theorem put_clock_shape (t : Trie) (key data : List Bool) :
    (put t key data).clock=20*(key.length+1)+(SemiprimeSourceCompactBits.copy data).clock := by
  induction key generalizing t with
  | nil => simp only [put,List.length_nil];omega
  | cons b bs ih => simp only [put,List.length_cons,ih];omega

/-- Actual insertion is linear in actual key and raw payload cells. -/
theorem put_clock (t : Trie) (key data : List Bool) :
    (put t key data).clock ≤ 20*key.length+3*data.length+21 := by
  rw [put_clock_shape,SemiprimeSourceCompactBits.copy_clock]
  omega

end RiemannGaussian.SemiprimeSourceHistogramTrieStore
