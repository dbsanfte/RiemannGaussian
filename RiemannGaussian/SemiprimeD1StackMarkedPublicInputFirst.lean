/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputCopies
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputShift
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputMetadata
/-! # Complete physical first-side marking branch -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputFirst
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInputCopies SemiprimeD1StackMarkedPublicInputCalls
open SemiprimeD1StackMarkedPublicInputShift SemiprimeD1StackMarkedPublicInputMetadata
open SemiprimeD1StackMarkedPublicInputPrimitives SemiprimeD1StackProcedureTrace
/-- Actual nonempty shift count from the retained ell/radix and descriptor index. -/
def shiftCount (bits raw indexWord : List Bool) : Nat :=
  (ellWord bits raw indexWord).length+indexWord.length*(radixWord bits raw indexWord).length
/-- The physically stopped branch still retains the copied raw suffix and
full digit until the later explicit cleanup. -/
def firstWork (bits raw indexWord : List Bool) : Work :=
  { reader := raw.drop (SemiprimeD1StackPublicInputMeaning.cached bits).length, digit := SemiprimeD1StackPublicInputMeaning.word bits raw, radix := radixWord bits raw indexWord, side := [false], shifted := marked (shiftCount bits raw indexWord) (SemiprimeD1StackPublicInputMeaning.word bits raw) }
/-- Sum of actual preserving copies, extraction, product cap, marker pops,
binary zero pushes and the low-bit replacement; no old report clock occurs. -/
def firstBound (bits raw indexWord : List Bool) : Nat :=
  (5*raw.length+4)+
  (SemiprimeD1StackWordBlockExecution.totalTime (SemiprimeD1StackPublicInputMeaning.cached bits)+1)+
  (5*indexWord.length+4)+(5*(radixWord bits raw indexWord).length+4)+
  (5*(indexWord.length*(2*(radixWord bits raw indexWord).length+3)+1)+1)+
  (5*(ellWord bits raw indexWord).length+4)+
  (5*(SemiprimeD1StackPublicInputMeaning.word bits raw).length+4)+
  (2*shiftCount bits raw indexWord+1)+2
/-- Complete actual reacquisition and first-side mark, with all real returns. -/
theorem first_run (bits raw indexWord : List Bool) (hb : bits≠[]) :
    ∃ t ≤ firstBound bits raw indexWord, Runs program t (ctl .raw) (data (acquired bits raw indexWord) {side := [false]})
        (ctl .widthA) (data (acquired bits raw indexWord) (firstWork bits raw indexWord)) := by
  let p := acquired bits raw indexWord
  let w0 : Work := {side := [false]}
  let w1 : Work := {side := [false], reader := raw.drop (SemiprimeD1StackPublicInputMeaning.cached bits).length, digit := SemiprimeD1StackPublicInputMeaning.word bits raw}
  let w2 : Work := {w1 with multiplier := indexWord}
  let w3 : Work := {w1 with radix := radixWord bits raw indexWord, offset := List.replicate (indexWord.length*(radixWord bits raw indexWord).length) true}
  let count := ellWord bits raw indexWord++
    List.replicate (indexWord.length*(radixWord bits raw indexWord).length) true
  let w4 : Work := {w3 with offset := count}
  let digit := SemiprimeD1StackPublicInputMeaning.word bits raw
  have h0 := raw_copy p w0
  have h1 := block_call p w0 raw
  have h2 := index_copy p w1
  have h3 := radix_copy p w2
  obtain ⟨q,hq,h4⟩ := product_call p w1 indexWord (radixWord bits raw indexWord)
  have h5 := offset_copy p w3
  have h6 := digit_copy p w4
  have h7 := shift_run p w3 count digit
  have hl : count.length=shiftCount bits raw indexWord := by
    simp only [count,shiftCount,List.length_append,List.length_replicate]
  have h8 := low_run p w3 (shiftCount bits raw indexWord)
    (shift_positive bits raw indexWord hb) digit
  rw [hl] at h7
  have h01 := join h0 h1
  have h23 := join h2 h3
  have h45 := join h4 h5
  have h67 := join h6 h7
  have hh := join (join (join (join (join h01 h23) h45) h67) h8) (runs_refl program (ctl .widthA) (data p (firstWork bits raw indexWord)))
  refine ⟨_,?_,hh⟩
  · dsimp only [p,w0,w1,w2,w3,w4,digit,count,firstBound,shiftCount] at hq ⊢
    rw [raw_word,index_word,modulus_word]
    dsimp only [ellWord,radixWord,shiftCount] at hq ⊢
    omega
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputFirst

