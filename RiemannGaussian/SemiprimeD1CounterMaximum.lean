/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramSquaresBounds
import RiemannGaussian.SemiprimeBitIndexClipping

/-! # Actual binary maximum of acquired D1 collision counters
Every present terminal is visited, including terminals at internal trie nodes.
Absent classes contribute zero. No complete pair-label catalogue, native maximum
encoding, supplied frequency or word-length oracle controls execution.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1CounterMaximum
open SemiprimeBitArithmetic SemiprimeBitIndexClipping
open SemiprimeSourceCompactBits (Compact)
open SemiprimeSourceHistogramTrie (Trie stored value nodes CompactCounters)
open SemiprimeSourceHistogramTrieBounds (CountCap)

/-- Compare both actual unsigned payloads and physically copy the larger one. -/
def maxWords (left right : List Bool) : SemiprimeSourceCompactBits.Report :=
  let order := leSignedBits ⟨false,left⟩ ⟨false,right⟩
  let out := SemiprimeSourceCompactBits.copy (if order.le then right else left)
  ⟨out.bits,order.clock+out.clock+3⟩

/-- The physical branch is exactly ordinary unsigned order, including zero. -/
theorem unsigned_order (left right : List Bool) :
    (leSignedBits ⟨false,left⟩ ⟨false,right⟩).le=true ↔ bitValue left≤bitValue right := by
  have h := leSignedBits_exact ⟨false,left⟩ ⟨false,right⟩
  change _ ↔ (bitValue left:ℤ)≤(bitValue right:ℤ) at h
  exact_mod_cast h

/-- No native maximum is executed to obtain the returned bits. -/
theorem maxWords_value (left right : List Bool) :
    bitValue (maxWords left right).bits=max (bitValue left) (bitValue right) := by
  unfold maxWords
  dsimp only
  rw [SemiprimeSourceCompactBits.copy_bits]
  split_ifs with h
  · exact (Nat.max_eq_right ((unsigned_order left right).mp h)).symm
  · have hn : bitValue right≤bitValue left := by
      have hnot := (unsigned_order left right).not.mp h
      omega
    exact (Nat.max_eq_left hn).symm

/-- Physically copied compact counters stay compact. -/
theorem maxWords_compact (left right : List Bool) (hl : Compact left) (hr : Compact right) :
    Compact (maxWords left right).bits := by
  unfold maxWords
  dsimp only
  rw [SemiprimeSourceCompactBits.copy_bits]
  split_ifs <;> assumption

/-- The selected payload is an actual input, so its width is derived. -/
theorem maxWords_length (left right : List Bool) (W : ℕ)
    (hl : left.length≤W) (hr : right.length≤W) : (maxWords left right).bits.length≤W := by
  unfold maxWords
  dsimp only
  rw [SemiprimeSourceCompactBits.copy_bits]
  split_ifs <;> assumption

/-- Both complete borrows/zero scans and the selected payload copy are paid. -/
theorem maxWords_clock (left right : List Bool) (W : ℕ)
    (hl : left.length≤W) (hr : right.length≤W) : (maxWords left right).clock≤44*(W+1) := by
  have hc := leSignedBits_cost (left:=⟨false,left⟩) (right:=⟨false,right⟩) hl hr
  have hs : (if (leSignedBits ⟨false,left⟩ ⟨false,right⟩).le then right else left).length≤W := by
    split_ifs <;> assumption
  simp only [maxWords,SemiprimeSourceCompactBits.copy_clock]
  omega

/-- Visit both actual children and the actual optional terminal payload. -/
def maximumTrie : Trie → SemiprimeSourceCompactBits.Report
  | .empty => ⟨[],1⟩
  | .node payload left right =>
    let l := maximumTrie left
    let r := maximumTrie right
    let children := maxWords l.bits r.bits
    let out := maxWords (payload.getD []) children.bits
    ⟨out.bits,l.clock+r.clock+children.clock+out.clock+5⟩

/-- All terminal counters, not just leaf terminals, are included. -/
theorem maximumTrie_node (p : Option (List Bool)) (l r : Trie) :
    bitValue (maximumTrie (.node p l r)).bits=
      max (bitValue (p.getD []))
        (max (bitValue (maximumTrie l).bits) (bitValue (maximumTrie r).bits)) := by
  simp only [maximumTrie,maxWords_value]

/-- Original counter bounds control the executed maximum without a value oracle. -/
theorem maximumTrie_le (t : Trie) (K : ℕ) (ht : CountCap t K) :
    bitValue (maximumTrie t).bits≤K := by
  induction t with
  | empty => exact Nat.zero_le _
  | node p l r ihl ihr =>
    rw [maximumTrie_node]
    exact max_le (ht []) (max_le (ihl (fun key => ht (false::key)))
      (ihr (fun key => ht (true::key))))

/-- The executed maximum dominates every actual stored counter, including absence. -/
theorem lookup_le_maximum (t : Trie) (key : List Bool) :
    value t key≤bitValue (maximumTrie t).bits := by
  induction t generalizing key with
  | empty => simp [value,SemiprimeSourceHistogramTrie.stored_empty,maximumTrie,bitValue]
  | node p l r ihl ihr =>
    rw [maximumTrie_node]
    cases key with
    | nil => exact le_max_left _ _
    | cons b key =>
      cases b with
      | false => exact (ihl key).trans ((le_max_left _ _).trans (le_max_right _ _))
      | true => exact (ihr key).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Intrinsic compactness of every original stored counter gives compact maximum bits. -/
theorem maximumTrie_compact (t : Trie) (ht : CompactCounters t) :
    Compact (maximumTrie t).bits := by
  induction t with
  | empty => trivial
  | node p l r ihl ihr =>
    apply maxWords_compact
    · exact ht []
    · exact maxWords_compact _ _ (ihl (fun key => ht (false::key)))
        (ihr (fun key => ht (true::key)))

/-- Maximum width comes from the actual terminal payloads. -/
theorem maximumTrie_length (t : Trie) (W : ℕ) (ht : ∀key,(stored t key).length≤W) :
    (maximumTrie t).bits.length≤W := by
  induction t with
  | empty => exact Nat.zero_le _
  | node p l r ihl ihr =>
    apply maxWords_length
    · exact ht []
    · exact maxWords_length _ _ W (ihl (fun key => ht (false::key)))
        (ihr (fun key => ht (true::key)))

/-- Actual finite-node traversal with linear word comparisons and all copies. -/
theorem maximumTrie_clock (t : Trie) (W : ℕ) (ht : ∀key,(stored t key).length≤W) :
    (maximumTrie t).clock≤nodes t*(88*(W+1)+7)+1 := by
  induction t with
  | empty => simp [maximumTrie,nodes]
  | node p l r ihl ihr =>
    have hl := ihl (fun key => ht (false::key))
    have hr := ihr (fun key => ht (true::key))
    have hll := maximumTrie_length l W (fun key => ht (false::key))
    have hrl := maximumTrie_length r W (fun key => ht (true::key))
    have hc := maxWords_clock _ _ W hll hrl
    have hcl := maxWords_length _ _ W hll hrl
    have hp := maxWords_clock (p.getD []) _ W (ht []) hcl
    simp only [maximumTrie,nodes]
    nlinarith

/-- Retain the actual acquired histogram/key producer and visit its trie once. -/
def maxState (state : SemiprimeSourceHistogramSquares.State) : SemiprimeSourceCompactBits.Report :=
  let out := maximumTrie state.trie
  ⟨out.bits,state.clock+out.clock+3⟩

/-- A genuine acquired state report is preserved even though the square word is unused. -/
theorem maxState_retains (state : SemiprimeSourceHistogramSquares.State) :
    state.clock≤(maxState state).clock := by
  simp only [maxState]
  omega

end RiemannGaussian.SemiprimeD1CounterMaximum
