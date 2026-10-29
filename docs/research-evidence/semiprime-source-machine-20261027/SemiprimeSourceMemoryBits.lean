/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRationalBits
import RiemannGaussian.SemiprimeBitProductSort

/-! # Boolean-addressed sequential source memory
Addresses are physical Boolean words. Every visited rational payload is copied,
every address test and decrement is executed, and all work is retained. Natural
indices appear only in the correctness specification. This is an explicit memory
primitive for the source instruction simulation, not a whole-machine theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeSourceMemoryBits
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitPrimeScan
open SemiprimeBitIndexClipping SemiprimeBitIndexTraversal SemiprimeRationalBits

/-- Actual full copy of both rational words and the sign flag. -/
def copyWord (x : RationalWord) : RationalReport :=
  let n := fitBits x.numerator.magnitude x.numerator.magnitude
  let d := fitBits x.denominator x.denominator
  ⟨⟨⟨x.numerator.negative,n.bits⟩,d.bits⟩,bitCost n+bitCost d+4⟩

/-- Physical copying retains every supplied bit, including high zero padding. -/
theorem copyWord_word (x : RationalWord) : (copyWord x).word=x := by
  simp only [copyWord,SemiprimeBitProductSort.fitBits_self]

/-- The full payload scan/copy cost follows from its actual word widths. -/
theorem copyWord_clock (x : RationalWord) (W : ℕ) (hx : Width x W) :
    (copyWord x).clock≤8*W+6 := by
  have hn := fitBits_cost x.numerator.magnitude x.numerator.magnitude
  have hd := fitBits_cost x.denominator x.denominator
  dsimp only [copyWord]
  rcases hx with ⟨hxn,hxd⟩
  omega

/-- Sequential access with a physical address counter, copying every visited payload.
Out-of-range access returns the fixed literal rational zero. -/
def readWord : List RationalWord → List Bool → RationalReport
  | [],_ => ⟨SemiprimeRationalBits.zeroWord,4⟩
  | x::xs,address =>
    let visit := copyWord x
    let test := nonzeroBits address
    if test.nonzero then
      let decrement := subBits address [true] false
      let rest := readWord xs decrement.result.bits
      ⟨rest.word,visit.clock+test.clock+bitCost decrement.result+rest.clock+6⟩
    else ⟨visit.word,visit.clock+test.clock+4⟩

/-- Exact finite memory lookup, with all indexing confined to the proof. -/
theorem readWord_word (xs : List RationalWord) (address : List Bool) :
    (readWord xs address).word=(xs[bitValue address]?).getD SemiprimeRationalBits.zeroWord := by
  induction xs generalizing address with
  | nil => simp [readWord]
  | cons x xs ih =>
    by_cases h : (nonzeroBits address).nonzero=true
    · have hp := (nonzeroBits_correct address).mp h
      have hd := (decrementBits_value hp).2
      have he : bitValue address=(bitValue address-1)+1 := by omega
      simp only [readWord,h,ite_true,ih,hd]
      conv_rhs => rw [he]
      rw [List.getElem?_cons_succ]
    · have hz := (nonzeroBits_false_iff address).mp (Bool.eq_false_of_not_eq_true h)
      simp only [readWord,Bool.eq_false_of_not_eq_true h,Bool.false_eq_true,ite_false,copyWord_word,hz,List.getElem?_cons_zero,Option.getD_some]

/-- Valid finite memory and its zero default give a valid result, at any address. -/
theorem readWord_valid (xs : List RationalWord) (address : List Bool)
    (hx : ∀ x∈xs,x.Valid) : (readWord xs address).word.Valid := by
  rw [readWord_word]
  cases he : xs[bitValue address]? with
  | none => change 0<(1:ℕ); omega
  | some x => exact hx x (List.mem_of_getElem? he)

/-- The selected payload has bounded physical width, including the literal default. -/
theorem readWord_width (xs : List RationalWord) (address : List Bool) (W : ℕ)
    (hW : 1≤W) (hx : ∀ x∈xs,Width x W) : Width (readWord xs address).word W := by
  rw [readWord_word]
  cases he : xs[bitValue address]? with
  | none => exact ⟨by simp [SemiprimeRationalBits.zeroWord],by simpa [SemiprimeRationalBits.zeroWord] using hW⟩
  | some x => exact hx x (List.mem_of_getElem? he)

/-- Both address and payload work are charged at every visited memory cell. -/
theorem readWord_clock (xs : List RationalWord) (address : List Bool) (W B : ℕ)
    (hB : 1≤B) (ha : address.length≤B) (hx : ∀ x∈xs,Width x W) :
    (readWord xs address).clock≤(xs.length+1)*(8*W+15*B+30) := by
  induction xs generalizing address with
  | nil => simp only [readWord,List.length_nil]; omega
  | cons x xs ih =>
    have hv := copyWord_clock x W (hx x List.mem_cons_self)
    have ht := nonzeroBits_cost address
    have hd := subBits_cost address [true] false
    have hlen : (subBits address [true] false).result.bits.length≤B := by
      rw [(subBits_counts address [true] false).2.2.2.2]
      simp only [List.length_cons,List.length_nil]
      exact max_le ha hB
    have hc := ih (subBits address [true] false).result.bits hlen
      (fun y hy => hx y (List.mem_cons_of_mem x hy))
    have hmax : max address.length [true].length≤B := max_le ha (by simpa using hB)
    simp only [readWord,List.length_cons]
    split_ifs <;> dsimp only <;> nlinarith

/-- Actual copies of all memory cells; used to charge persistence/relocation explicitly. -/
structure CopyReport where
  /-- Copied payloads. -/
  words : List RationalWord
  /-- All bit copies and list constructor/branch operations. -/
  clock : ℕ

/-- A complete sequential memory copy, without a sharing requirement. -/
def copyMemory : List RationalWord → CopyReport
  | [] => ⟨[],1⟩
  | x::xs =>
    let head := copyWord x
    let tail := copyMemory xs
    ⟨head.word::tail.words,head.clock+tail.clock+3⟩

/-- The copied finite store is physically identical. -/
theorem copyMemory_words (xs : List RationalWord) : (copyMemory xs).words=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [copyMemory,copyWord_word,ih]

/-- Entire-store copying has a derived bound in actual cells and physical word width. -/
theorem copyMemory_clock (xs : List RationalWord) (W : ℕ) (hx : ∀ x∈xs,Width x W) :
    (copyMemory xs).clock≤xs.length*(8*W+9)+1 := by
  induction xs with
  | nil => simp [copyMemory]
  | cons x xs ih =>
    have hh := copyWord_clock x W (hx x List.mem_cons_self)
    have ht := ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
    simp only [copyMemory,List.length_cons]
    nlinarith

end RiemannGaussian.SemiprimeSourceMemoryBits
