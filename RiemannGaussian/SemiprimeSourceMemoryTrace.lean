/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceProgramStorage

/-! # Actual auxiliary scan and copy frames
These proof-view traces follow the SAME branch and decrement as readWord.
They retain visited copies, address/test/decrement fields, return words and
outer report counters. Primitive Boolean/arithmetic internal scratch is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourceMemoryTrace
open SemiprimeRationalBits SemiprimeSourceMemoryBits SemiprimeSourceProgramStorage
open SemiprimeBitArithmetic SemiprimeBitDivision

/-- Concrete fields of one actually visited read frame, including its return. -/
structure ReadFrame where
  /-- Actual original address at this recursion level. -/
  address : List Bool
  /-- Actual copied visited payload. -/
  visited : RationalWord
  /-- The computed nonzero-test Boolean. -/
  nonzero : Bool
  /-- Actual decremented address, empty if no decrement occurs. -/
  decrement : List Bool
  /-- Actual final subtraction borrow, false when no subtraction occurs. -/
  borrow : Bool
  /-- Actual pending memory tail; counted expanded, without a sharing assumption. -/
  pending : List RationalWord
  /-- Actual word returned at this recursion level. -/
  returned : RationalWord
  /-- Actual enclosing and auxiliary report-counter fields. -/
  ledger : List ℕ

/-- The same visit/test/decrement/recursive-result fields as the original scan. -/
def readFrame (x : RationalWord) (xs : List RationalWord) (address : List Bool) : ReadFrame :=
  let visit := copyWord x
  let test := nonzeroBits address
  if test.nonzero then
    let dec := subBits address [true] false
    let rest := readWord xs dec.result.bits
    ⟨address,visit.word,test.nonzero,dec.result.bits,dec.borrow,xs,rest.word,
      [visit.clock,test.clock,dec.result.gates,dec.result.reads,dec.result.writes,
        dec.result.tests,rest.clock,(readWord (x::xs) address).clock]⟩
  else ⟨address,visit.word,test.nonzero,[],false,xs,visit.word,
      [visit.clock,test.clock,(readWord (x::xs) address).clock]⟩

/-- Actual visited-frame sequence; zero-address termination does not scan the tail. -/
def readFrames : List RationalWord → List Bool → List ReadFrame
  | [],_ => []
  | x::xs,address =>
    let frame := readFrame x xs address
    if (nonzeroBits address).nonzero then
      frame::readFrames xs (subBits address [true] false).result.bits
    else [frame]

/-- The auxiliary trace visits no more cells than the actual input store. -/
theorem readFrames_length (memory : List RationalWord) (address : List Bool) :
    (readFrames memory address).length ≤ memory.length := by
  induction memory generalizing address with
  | nil => simp [readFrames]
  | cons x xs ih =>
    simp only [readFrames,List.length_cons]
    split_ifs
    · simpa only [List.length_cons] using Nat.add_le_add_right (ih _) 1
    · simp

/-- Every stored clock field is dominated in aggregate by twice the actual enclosing report. -/
theorem frame_ledger (x : RationalWord) (xs : List RationalWord) (address : List Bool) :
    (readFrame x xs address).ledger.sum ≤ 2*(readWord (x::xs) address).clock ∧
      (readFrame x xs address).ledger.length ≤ 8 := by
  simp only [readFrame,readWord,bitCost]
  split_ifs <;> simp only [List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] <;> omega

/-- Actual binary sizes of all stored Nat report counters are bounded by the
conservative unary ledger, including zero counters. -/
theorem ledger_binary_cells (ns : List ℕ) :
    (ns.map Nat.size).sum ≤ ns.sum+ns.length := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    have hn : n.size ≤ n+1 := Nat.size_le.mpr ((Nat.lt_succ_self n).trans (Nat.lt_two_pow_self (n:=n+1)))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- Both actual payload words and both physical address fields have original bounds. -/
theorem frame_width (x : RationalWord) (xs : List RationalWord) (address : List Bool)
    (W B : ℕ) (hW : 1 ≤ W) (hB : 1 ≤ B) (ha : address.length ≤ B)
    (hx : ∀ y∈x::xs,Width y W) :
    Width (readFrame x xs address).visited W ∧
      Width (readFrame x xs address).returned W ∧
      (readFrame x xs address).address.length ≤ B ∧
      (readFrame x xs address).decrement.length ≤ B := by
  have hv := hx x List.mem_cons_self
  have ht := readWord_width xs (subBits address [true] false).result.bits W hW
    (fun y hy => hx y (List.mem_cons_of_mem x hy))
  have hd : (subBits address [true] false).result.bits.length ≤ B := by
    rw [(subBits_counts address [true] false).2.2.2.2]
    simpa only [List.length_cons,List.length_nil] using max_le ha hB
  simp only [readFrame,copyWord_word]
  split_ifs
  · exact ⟨hv,ht,ha,hd⟩
  · exact ⟨hv,hv,ha,by simp⟩

/-- The saved recursive memory pointer is the actual original tail. -/
theorem frame_pending (x : RationalWord) (xs : List RationalWord) (address : List Bool) :
    (readFrame x xs address).pending=xs := by
  simp only [readFrame]
  split_ifs <;> rfl

/-- Conservative payload/tag/outer-counter field view. Counter magnitudes are
charged in unary, which also bounds binary storage; no arithmetic scratch implied. -/
def frameCells (f : ReadFrame) : ℕ :=
  wordCells f.visited+wordCells f.returned+memoryCells f.pending+f.pending.length+
    f.address.length+f.decrement.length+
    f.ledger.sum+f.ledger.length+9

/-- One actual frame has an original-data bound, with all its counter fields included. -/
theorem frameCells_bound (x : RationalWord) (xs : List RationalWord) (address : List Bool)
    (W B C : ℕ) (hW : 1 ≤ W) (hB : 1 ≤ B) (ha : address.length ≤ B)
    (hx : ∀ y∈x::xs,Width y W) (hc : (readWord (x::xs) address).clock ≤ C) :
    frameCells (readFrame x xs address) ≤ (x::xs).length*(2*W+2)+4*W+2*B+2*C+19 := by
  obtain ⟨hv,hr,had,hdec⟩ := frame_width x xs address W B hW hB ha hx
  have hl := frame_ledger x xs address
  have hp := memoryCells_bound xs W (fun y hy => hx y (List.mem_cons_of_mem x hy))
  unfold frameCells wordCells
  rw [frame_pending]
  simp only [List.length_cons]
  rcases hv with ⟨hvn,hvd⟩
  rcases hr with ⟨hrn,hrd⟩
  nlinarith

/-- Every actual recursive scan frame has a polynomial original M,W,B cap. -/
theorem readFrames_cells (memory : List RationalWord) (address : List Bool)
    (W B : ℕ) (hW : 1 ≤ W) (hB : 1 ≤ B) (ha : address.length ≤ B)
    (hx : ∀ y∈memory,Width y W) :
    ((readFrames memory address).map frameCells).sum ≤
      memory.length*(memory.length*(2*W+2)+4*W+2*B+2*((memory.length+1)*(8*W+15*B+30))+19) := by
  induction memory generalizing address with
  | nil => simp [readFrames]
  | cons x xs ih =>
    have hc := readWord_clock (x::xs) address W B hB ha hx
    have hf := frameCells_bound x xs address W B
      (( (x::xs).length+1)*(8*W+15*B+30)) hW hB ha hx hc
    have hd : (subBits address [true] false).result.bits.length ≤ B := by
      rw [(subBits_counts address [true] false).2.2.2.2]
      simpa only [List.length_cons,List.length_nil] using max_le ha hB
    have ht := ih _ hd (fun y hy => hx y (List.mem_cons_of_mem x hy))
    simp only [readFrames]
    split_ifs
    · simp only [List.map_cons,List.sum_cons,List.length_cons] at hf ht ⊢
      nlinarith
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      exact hf.trans (Nat.le_mul_of_pos_left _ (by simp))

/-- Every actual copyMemory recursion return, including the empty base return. -/
def copyReturns : List RationalWord → List CopyReport
  | [] => [copyMemory []]
  | x::xs => copyMemory (x::xs)::copyReturns xs

/-- Copy return-frame count is exactly original memory length plus one. -/
theorem copyReturns_length (memory : List RationalWord) :
    (copyReturns memory).length=memory.length+1 := by
  induction memory with
  | nil => rfl
  | cons x xs ih => simp only [copyReturns,List.length_cons,ih]

/-- Each actual return list/counter is bounded from original memory, not a
supplied reachable-state predicate. -/
theorem copyReturns_bound (memory : List RationalWord) (W : ℕ)
    (hx : ∀ x∈memory,Width x W) (r : CopyReport) (hr : r∈copyReturns memory) :
    r.words.length ≤ memory.length ∧ (∀ x∈r.words,Width x W) ∧
      r.clock ≤ memory.length*(8*W+9)+1 := by
  induction memory with
  | nil =>
    simp only [copyReturns,List.mem_singleton] at hr
    subst r
    simp [copyMemory]
  | cons x xs ih =>
    simp only [copyReturns,List.mem_cons] at hr
    rcases hr with rfl|hr
    · refine ⟨?_,?_,copyMemory_clock _ W hx⟩
      · rw [copyMemory_words]
      · simpa only [copyMemory_words] using hx
    · have ht := ih (fun y hy => hx y (List.mem_cons_of_mem x hy)) hr
      refine ⟨by simpa only [List.length_cons] using ht.1.trans (Nat.le_succ _),ht.2.1,?_⟩
      exact ht.2.2.trans (by simp only [List.length_cons]; nlinarith)

/-- A return frame retains actual list payloads/spines and outer counter fields.
The counter magnitude is conservatively charged unary. -/
def copyReturnCells (r : CopyReport) : ℕ := memoryCells r.words+r.words.length+r.clock+3

/-- All actual copied return frames, retaining duplicate lists conservatively,
have a fixed polynomial original memory/width bound. -/
theorem copyReturns_cells (memory : List RationalWord) (W : ℕ)
    (hx : ∀ x∈memory,Width x W) :
    ((copyReturns memory).map copyReturnCells).sum ≤
      (memory.length+1)*(memory.length*(2*W+1)+memory.length+
        memory.length*(8*W+9)+4) := by
  have each (r : CopyReport) (hr : r∈copyReturns memory) :
      copyReturnCells r ≤ memory.length*(2*W+1)+memory.length+
        memory.length*(8*W+9)+4 := by
    have hb := copyReturns_bound memory W hx r hr
    have hp := (memoryCells_bound r.words W hb.2.1).trans
      (Nat.mul_le_mul_right (2*W+1) hb.1)
    unfold copyReturnCells
    omega
  have sum_bound (rs : List CopyReport) (C : ℕ)
      (h : ∀ r∈rs,copyReturnCells r ≤ C) :
      (rs.map copyReturnCells).sum ≤ rs.length*C := by
    induction rs with
    | nil => simp
    | cons r rs ih =>
      have hh := h r List.mem_cons_self
      have ht := ih (fun x hx => h x (List.mem_cons_of_mem r hx))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  simpa only [copyReturns_length] using sum_bound (copyReturns memory) _ each

end RiemannGaussian.SemiprimeSourceMemoryTrace
