/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramTrieStore
import RiemannGaussian.SemiprimeSourceCompactWordIds

/-! # Actual reverse-prefix physical ID dictionary
The tail is acquired once. Its compact next-key counter is used for insertion,
so key zero stores the oldest ID. Pointer/tape implementation remains separate.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramPrefix
open SemiprimeSourceHistogramTrie SemiprimeBitArithmetic
open SemiprimeSourceCompactBits (Compact)

/-- Cached prefix dictionary and its next compact variable key. -/
structure State where
  /-- Next unused original-variable key. -/
  nextKey : List Bool
  /-- Physical selected-ID dictionary. -/
  trie : Trie
  /-- Retained recursive, payload-copy and counter reports. -/
  clock : ℕ

/-- Acquire every actual selected ID once, oldest first. -/
def acquire : List (List Bool) → State
  | [] => ⟨[], .empty, 1⟩
  | id::ids =>
    let prev := acquire ids
    let label := SemiprimeSourceCompactBits.trim id
    let written := SemiprimeSourceHistogramTrieStore.put prev.trie prev.nextKey label.bits
    let next := SemiprimeSourceCompactBits.increment prev.nextKey
    ⟨next.bits, written.trie, prev.clock+label.clock+written.clock+next.clock+8⟩

/-- The actual next key counts the input prefix. -/
theorem next_value (ids : List (List Bool)) :
    bitValue (acquire ids).nextKey = ids.length := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    simp only [acquire, SemiprimeSourceCompactBits.increment_value, ih, List.length_cons]

/-- Every generated variable key has canonical compact bytes. -/
theorem next_compact (ids : List (List Bool)) : Compact (acquire ids).nextKey := by
  cases ids with
  | nil => trivial
  | cons id ids => exact SemiprimeSourceCompactBits.increment_compact _

/-- Every stored selected ID is normalized by the actual trim call. -/
theorem stored_compact (ids : List (List Bool)) : CompactCounters (acquire ids).trie := by
  induction ids with
  | nil => exact empty_compact
  | cons id ids ih =>
    exact SemiprimeSourceHistogramTrieStore.put_compact _ _ _ ih
      (SemiprimeSourceCompactBits.trim_compact id)

/-- Proof-side original reverse-prefix lookup, with empty absent value. -/
def expected (ids : List (List Bool)) (i : ℕ) : List Bool :=
  (SemiprimeSourceCompactBits.trim ((ids.reverse[i]?).getD [])).bits

private theorem getD_append_single (xs : List (List Bool)) (x : List Bool) (i : ℕ) :
    ((xs ++ [x])[i]?).getD [] = if i = xs.length then x else (xs[i]?).getD [] := by
  induction xs generalizing i with
  | nil => cases i <;> simp
  | cons y ys ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

private theorem expected_cons (id : List Bool) (ids : List (List Bool)) (i : ℕ) :
    expected (id::ids) i = if i = ids.length then
      (SemiprimeSourceCompactBits.trim id).bits else expected ids i := by
  simp only [expected, List.reverse_cons, getD_append_single, List.length_reverse]
  split <;> rfl

/-- Exact reverse-prefix dictionary at every compact physical query key. -/
theorem stored_eq (ids : List (List Bool)) (key : List Bool) (hk : Compact key) :
    stored (acquire ids).trie key = expected ids (bitValue key) := by
  induction ids with
  | nil => simp [acquire, stored_empty, expected, SemiprimeSourceCompactBits.trim]
  | cons id ids ih =>
    have he : key = (acquire ids).nextKey ↔ bitValue key = ids.length := by
      constructor
      · intro h; rw [h, next_value]
      · intro h
        exact SemiprimeSourceCompactWordIds.compact_value_injective _ _ hk
          (next_compact ids) (h.trans (next_value ids).symm)
    simp only [acquire, SemiprimeSourceHistogramTrieStore.put_stored,
      expected_cons, he, ih]

/-- Paid physical lookup returns that exact normalized original ID. -/
theorem lookup_eq (ids : List (List Bool)) (key : List Bool) (hk : Compact key) :
    (lookup (acquire ids).trie key).bits = expected ids (bitValue key) := by
  rw [lookup_bits, stored_eq ids key hk]

/-- No key width grows linearly with the number of increments. -/
theorem next_length (ids : List (List Bool)) :
    (acquire ids).nextKey.length ≤ Nat.clog 2 (ids.length+1) := by
  simpa only [next_value] using
    SemiprimeSourceCompactBits.compact_length_clog _ (next_compact ids)

/-- Every stored payload is bounded by the original input ID width. -/
theorem stored_length (ids : List (List Bool)) (B : ℕ)
    (hi : ∀ id ∈ ids, id.length ≤ B) (key : List Bool) :
    (stored (acquire ids).trie key).length ≤ B := by
  induction ids generalizing key with
  | nil => simp [acquire, stored_empty]
  | cons id ids ih =>
    apply SemiprimeSourceHistogramTrieStore.put_width
    · exact fun query => ih (fun x hx => hi x (List.mem_cons_of_mem id hx)) query
    · exact (SemiprimeSourceCompactBits.trim_length id).trans (hi id (by simp))

/-- A common original prefix-size cap bounds every generated key. -/
theorem next_length_cap (ids : List (List Bool)) (K : ℕ) (hk : ids.length ≤ K) :
    (acquire ids).nextKey.length ≤ SemiprimeSourceHistogramTrieBounds.clockWidth K := by
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ (next_compact ids)
  rw [next_value]
  have hp := Nat.le_pow_clog (by decide : 1 < (2:ℕ)) (K+2)
  change ids.length < 2 ^ Nat.clog 2 (K+2)
  omega

/-- Only the actually traversed key paths allocate dictionary nodes. -/
theorem nodes_bound (ids : List (List Bool)) (K : ℕ) (hk : ids.length ≤ K) :
    nodes (acquire ids).trie ≤
      ids.length * (SemiprimeSourceHistogramTrieBounds.clockWidth K+1) := by
  induction ids with
  | nil => simp [acquire, nodes]
  | cons id ids ih =>
    have ht : ids.length ≤ K := by simp only [List.length_cons] at hk; omega
    have hn := SemiprimeSourceHistogramTrieStore.put_nodes (acquire ids).trie
      (acquire ids).nextKey (SemiprimeSourceCompactBits.trim id).bits
    have hl := next_length_cap ids K ht
    have hp := ih ht
    change nodes (SemiprimeSourceHistogramTrieStore.put _ _ _).trie ≤ _
    simp only [List.length_cons]
    nlinarith

/-- Paid acquisition is linear in prefix length times ID and compact-key widths.
This includes actual trims, payload copies, insertion paths, and increments. -/
theorem acquire_clock (ids : List (List Bool)) (B K : ℕ)
    (hk : ids.length ≤ K) (hi : ∀ id ∈ ids, id.length ≤ B) :
    (acquire ids).clock ≤ ids.length *
      (100*(B+SemiprimeSourceHistogramTrieBounds.clockWidth K+2))+1 := by
  induction ids with
  | nil => simp [acquire]
  | cons id ids ih =>
    have ht : ids.length ≤ K := by simp only [List.length_cons] at hk; omega
    have hp := ih ht (fun x hx => hi x (List.mem_cons_of_mem id hx))
    have hl := next_length_cap ids K ht
    have hb := hi id (by simp)
    have htrim := SemiprimeSourceCompactBits.trim_length id
    have hput := SemiprimeSourceHistogramTrieStore.put_clock (acquire ids).trie
      (acquire ids).nextKey (SemiprimeSourceCompactBits.trim id).bits
    have hinc := SemiprimeSourceCompactBits.increment_clock (acquire ids).nextKey
      (SemiprimeSourceHistogramTrieBounds.clockWidth K)
      (SemiprimeSourceHistogramTrieBounds.clockWidth_pos K) hl
    have htr := SemiprimeSourceCompactBits.trim_clock id
    change (acquire ids).clock + _ + _ + _ + 8 ≤ _
    simp only [List.length_cons]
    nlinarith

end RiemannGaussian.SemiprimeSourceHistogramPrefix
