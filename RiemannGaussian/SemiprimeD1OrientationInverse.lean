/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OrientationBits

/-! # Actual physical inverse of the D1 orientation packet recipe
The inverse parses actual framed colour fields and reconstructs compact padding
bits. No semantic Word, colour value, padding answer or inverse oracle executes.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1OrientationInverse
open SemiprimeD1OrientationBits
open SemiprimeBitArithmetic SemiprimeBitIndexClipping
open SemiprimeSourceCompactBits (Compact)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Actual reconstructed rows/index plus all parsing/copy/arithmetic reports. -/
structure Decoded where
  /-- Reconstructed original owner colour fields. -/
  left : List (List Bool)
  /-- Reconstructed original factor colour fields. -/
  right : List (List Bool)
  /-- Reconstructed compact padding index. -/
  index : List Bool
  /-- Complete framing and sorted-field validity test. -/
  valid : Bool
  /-- Every parser, comparison, recursive stage, copy and trim report. -/
  clock : ℕ

/-- Parse exactly one coordinate per actual slot bit and reconstruct the two
physical ordered rows; equal coordinates insert the consumed low padding bit. -/
def recover : List Bool → List Bool → Decoded
  | key,[] =>
    let index := SemiprimeSourceCompactBits.copy key
    ⟨[],[],index.bits,true,index.clock+3⟩
  | key,bit::slots =>
    let field := SemiprimeSourceHistogramKeyBits.split key
    let colours := SemiprimeSourceHistogramKeyBits.split field.first
    let tail := recover field.rest slots
    let order := leSignedBits ⟨false,colours.first⟩ ⟨false,colours.rest⟩
    let eq := equality order
    let left := SemiprimeSourceCompactBits.copy
      (if eq then colours.first else if bit then colours.rest else colours.first)
    let right := SemiprimeSourceCompactBits.copy
      (if eq then colours.rest else if bit then colours.first else colours.rest)
    let index := if eq then SemiprimeSourceCompactBits.trim (bit::tail.index)
      else SemiprimeSourceCompactBits.copy tail.index
    ⟨left.bits::tail.left,right.bits::tail.right,index.bits,
      field.valid && colours.valid && tail.valid && order.le,
      field.clock+colours.clock+tail.clock+order.clock+left.clock+right.clock+index.clock+30⟩

/-- Physical trimming is the identity on every original compact magnitude. -/
theorem trim_eq (bits : List Bool) (h : Compact bits) :
    (SemiprimeSourceCompactBits.trim bits).bits=bits :=
  SemiprimeSourceCompactWordIds.compact_value_injective _ _
    (SemiprimeSourceCompactBits.trim_compact _) h (SemiprimeSourceCompactBits.trim_value _)

/-- Consuming an implicit leading zero and restoring it does not duplicate zero. -/
theorem restore_low_bit (j : List Bool) (hj : Compact j) :
    (SemiprimeSourceCompactBits.trim (j.headD false::j.tail)).bits=j := by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _
    (SemiprimeSourceCompactBits.trim_compact _) hj
  rw [SemiprimeSourceCompactBits.trim_value]
  cases j <;> rfl

/-- Actual consumed padding suffixes remain compact, with no intermediate advice. -/
theorem coordinate_next_compact (left right j : List Bool) (hj : Compact j) :
    Compact (coordinate left right j).next := by
  rw [coordinate_next]
  split_ifs
  · cases j with
    | nil => trivial
    | cons b bs => exact hj.1
  · exact hj

/-- Actual decoder's non-report data, for exact executed round-trip statements. -/
def value (out : Decoded) : List (List Bool) × List (List Bool) × List Bool × Bool :=
  (out.left,out.right,out.index,out.valid)

/-- Parsing one acquired framed coordinate has this exact data transition. -/
theorem recover_frame (low high key : List Bool) (bit : Bool) (slots : List Bool) :
    let tail := recover key slots
    let order := leSignedBits ⟨false,low⟩ ⟨false,high⟩
    let eq := equality order
    value (recover (frame (frame low high) key) (bit::slots))=
      ((if eq then low else if bit then high else low)::tail.left,
       (if eq then high else if bit then low else high)::tail.right,
       (if eq then (SemiprimeSourceCompactBits.trim (bit::tail.index)).bits else tail.index),
       tail.valid && order.le) := by
  dsimp only
  have hf := SemiprimeSourceHistogramKeyBits.split_frame (frame low high) key
  have hc := SemiprimeSourceHistogramKeyBits.split_frame low high
  simp only [recover,value,hf.1,hf.2.1,hf.2.2,hc.1,hc.2.1,hc.2.2,Bool.true_and]
  split_ifs <;> simp only [SemiprimeSourceCompactBits.copy_bits]

/-- Reconstruction round-trip on original same-length physical colour rows.
Only original padding compactness is assumed; no decoded answer is supplied. -/
theorem roundtrip_value (left right : List (List Bool)) (j : List Bool)
    (hlen : left.length=right.length) (hj : Compact j) :
    value (recover (acquire left right j).key (acquire left right j).slots)=(left,right,j,true) := by
  induction left generalizing right j with
  | nil =>
    cases right with
    | nil => simp [acquire,recover,value,SemiprimeSourceCompactBits.copy_bits]
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases right with
    | nil => simp at hlen
    | cons y ys =>
      let c := coordinate x y j
      let tail := acquire xs ys c.next
      have ht := ih ys c.next (by simpa using hlen) (coordinate_next_compact x y j hj)
      have htl : (recover tail.key tail.slots).left=xs := congrArg Prod.fst ht
      have htr : (recover tail.key tail.slots).right=ys := congrArg (fun z => z.2.1) ht
      have hti : (recover tail.key tail.slots).index=c.next := congrArg (fun z => z.2.2.1) ht
      have htv : (recover tail.key tail.slots).valid=true := congrArg (fun z => z.2.2.2) ht
      change value (recover (SemiprimeSourceHistogramKeyBits.pair c.field tail.key).bits
        (c.slot::tail.slots))=_
      rw [SemiprimeSourceHistogramKeyBits.pair_bits]
      have hfield : c.field=frame c.low c.high := coordinate_field x y j
      rw [hfield,recover_frame]
      rw [htl,htr,hti,htv]
      have hv := coordinate_flags x y j
      by_cases he : c.equal=true
      · have heq := hv.1.mp he
        have ho : c.ordered=true := hv.2.mpr heq.le
        have ho' : (leSignedBits ⟨false,x⟩ ⟨false,y⟩).le=true := ho
        have hl : c.low=x := by simpa only [ho',ite_true] using (coordinate_fields x y j).1
        have hr : c.high=y := by simpa only [ho',ite_true] using (coordinate_fields x y j).2
        have hs : c.slot=j.headD false := by
          change (if c.equal then j.headD false else !c.ordered)=_
          simp only [he,ite_true]
        have hn : c.next=j.tail := by
          change (if c.equal then j.tail else j)=_
          simp only [he,ite_true]
        have he' : equality (leSignedBits ⟨false,x⟩ ⟨false,y⟩)=true := he
        rw [hl,hr]
        simp only [he',ho',ite_true,Bool.true_and]
        rw [hs,hn,restore_low_bit j hj]
      · have heq : bitValue x≠bitValue y := fun h => he (hv.1.mpr h)
        have hcfalse : c.equal=false := Bool.eq_false_iff.mpr he
        have hn : c.next=j := by
          change (if c.equal then j.tail else j)=_
          simp only [hcfalse,Bool.false_eq_true,ite_false]
        have hs : c.slot= !c.ordered := by
          change (if c.equal then j.headD false else !c.ordered)=_
          simp only [hcfalse,Bool.false_eq_true,ite_false]
        cases ho : c.ordered with
        | false =>
          have ho' : (leSignedBits ⟨false,x⟩ ⟨false,y⟩).le=false := ho
          have hl : c.low=y := by simpa only [ho',Bool.false_eq_true,ite_false] using (coordinate_fields x y j).1
          have hr : c.high=x := by simpa only [ho',Bool.false_eq_true,ite_false] using (coordinate_fields x y j).2
          have hnot : ¬bitValue x≤bitValue y := (hv.2).not.mp (by rw [ho];decide)
          have hvord : (leSignedBits ⟨false,y⟩ ⟨false,x⟩).le=true :=
            (SemiprimeD1CounterMaximum.unsigned_order y x).mpr (by omega)
          have hveq : equality (leSignedBits ⟨false,y⟩ ⟨false,x⟩)=false := by
            apply Bool.eq_false_iff.mpr
            intro h
            exact heq ((equality_exact y x).mp h).symm
          rw [hl,hr]
          simp only [hveq,hvord,Bool.false_eq_true,ite_false,hs,ho,Bool.not_false,ite_true,Bool.true_and,hn]
        | true =>
          have ho' : (leSignedBits ⟨false,x⟩ ⟨false,y⟩).le=true := ho
          have hl : c.low=x := by simpa only [ho',ite_true] using (coordinate_fields x y j).1
          have hr : c.high=y := by simpa only [ho',ite_true] using (coordinate_fields x y j).2
          have hveq : equality (leSignedBits ⟨false,x⟩ ⟨false,y⟩)=false := hcfalse
          rw [hl,hr]
          simp only [hveq,ho',Bool.false_eq_true,ite_false,hs,ho,Bool.not_true,Bool.true_and,hn]

/-- Forward packet key plus slot bits determine both original rows and compact j. -/
theorem injective (left right left' right' : List (List Bool)) (j j' : List Bool)
    (hlen : left.length=right.length) (hlen' : left'.length=right'.length)
    (hj : Compact j) (hj' : Compact j')
    (hk : (acquire left right j).key=(acquire left' right' j').key)
    (hs : (acquire left right j).slots=(acquire left' right' j').slots) :
    left=left' ∧ right=right' ∧ j=j' := by
  have h := roundtrip_value left right j hlen hj
  rw [hk,hs,roundtrip_value left' right' j' hlen' hj'] at h
  simpa only [Prod.mk.injEq,and_true] using h.symm

end RiemannGaussian.SemiprimeD1OrientationInverse
