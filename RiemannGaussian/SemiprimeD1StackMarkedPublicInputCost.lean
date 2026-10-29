/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputExecution
/-! # Fixed own polynomial for every actually executed marked coefficient -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputCost
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInputFirst SemiprimeD1StackMarkedPublicInputFinish
open SemiprimeD1StackMarkedPublicInputMetadata SemiprimeD1StackMarkedPublicInputBody
open SemiprimeD1StackMarkedPublicInputExecution
/-- Actual original word bytes only; neither coefficient value nor an answer is input. -/
def inputSize (bits raw indexWord : List Bool) : Nat :=
  bits.length+raw.length+indexWord.length+2
/-- All actual paid metadata and full decoded-word lengths are linearly bounded. -/
theorem metadata_bounds (bits raw indexWord : List Bool) :
    (ellWord bits raw indexWord).length ≤ inputSize bits raw indexWord ∧
    (radixWord bits raw indexWord).length ≤ 66*inputSize bits raw indexWord ∧
    (SemiprimeD1StackPublicInputMeaning.cached bits).length ≤ 66*inputSize bits raw indexWord ∧
    (SemiprimeD1StackPublicInputMeaning.word bits raw).length ≤ 66*inputSize bits raw indexWord := by
  have hc := SemiprimeD1StackPublicZeroBounds.cached_length_le bits
  have hw := SemiprimeD1StackPublicZeroBounds.word_length bits raw
  have hd := Nat.div_le_self (SemiprimeMacroParameters.transformLength bits.length) 4
  have he := SemiprimeD1StackPublicZeroBounds.cached_length bits
  change (SemiprimeD1StackPublicInputMeaning.cached bits).length≤66*(bits.length+1) at hc
  change (SemiprimeD1StackPublicInputMeaning.word bits raw).length=(SemiprimeD1StackPublicInputMeaning.cached bits).length at hw
  change (SemiprimeD1StackPublicInputMeaning.cached bits).length=SemiprimeMacroParameters.transformLength bits.length+1 at he
  rw [ell_word,radix_word,List.length_replicate,List.length_replicate]
  unfold SemiprimeMacroParameters.radixBits at *
  dsimp only [inputSize]
  exact ⟨by omega,by omega,by omega,by omega⟩
/-- Unary offset materialization counts the actual index-times-radix marker product. -/
theorem shift_le (bits raw indexWord : List Bool) :
    shiftCount bits raw indexWord ≤ 67*(inputSize bits raw indexWord)^2 := by
  let s := inputSize bits raw indexWord
  have hs : 2 ≤ s := by dsimp [s,inputSize];omega
  have hi : indexWord.length ≤ s := by dsimp [s,inputSize];omega
  obtain ⟨he,hd,_,_⟩ := metadata_bounds bits raw indexWord
  have hm := Nat.mul_le_mul hi hd
  change indexWord.length*(radixWord bits raw indexWord).length ≤ s*(66*s) at hm
  unfold shiftCount
  change (ellWord bits raw indexWord).length+indexWord.length*(radixWord bits raw indexWord).length ≤ 67*s^2
  change (ellWord bits raw indexWord).length ≤ s at he
  nlinarith
/-- All real extraction/copy/product/shift instructions fit a fixed own quadratic. -/
theorem firstBound_le (bits raw indexWord : List Bool) :
    firstBound bits raw indexWord ≤ 100000*(inputSize bits raw indexWord)^2 := by
  let s := inputSize bits raw indexWord
  have hs : 2 ≤ s := by dsimp [s,inputSize];omega
  have hi : indexWord.length ≤ s := by dsimp [s,inputSize];omega
  have hr : raw.length ≤ s := by dsimp [s,inputSize];omega
  obtain ⟨he,hd,hc,hw⟩ := metadata_bounds bits raw indexWord
  have hm := Nat.mul_le_mul hi hd
  have hx := shift_le bits raw indexWord
  unfold firstBound
  rw [SemiprimeD1StackWordBlockBounds.totalTime_eq]
  change _ ≤ 100000*s^2
  change indexWord.length*(radixWord bits raw indexWord).length ≤ s*(66*s) at hm
  change (ellWord bits raw indexWord).length ≤ s at he
  change (radixWord bits raw indexWord).length ≤ 66*s at hd
  change (SemiprimeD1StackPublicInputMeaning.cached bits).length ≤ 66*s at hc
  change (SemiprimeD1StackPublicInputMeaning.word bits raw).length ≤ 66*s at hw
  change shiftCount bits raw indexWord ≤ 67*s^2 at hx
  nlinarith
/-- The real fitter pays every discarded high input cell as well as its width. -/
theorem fit_time_le (operand template : List Bool) :
    SemiprimeD1StackWordFitExecution.totalTime operand template ≤ 10*template.length+operand.length+8 := by
  have h : (operand.drop template.length).length ≤ operand.length := by rw [List.length_drop];omega
  unfold SemiprimeD1StackWordFitExecution.totalTime
  omega
/-- Full signal padding and all actual shifted zeros are included in the operand bytes. -/
theorem marked_length_le (bits raw indexWord : List Bool) :
    (marked (shiftCount bits raw indexWord) (SemiprimeD1StackPublicInputMeaning.word bits raw)).length ≤ 200*(inputSize bits raw indexWord)^2 := by
  have hs : 2 ≤ inputSize bits raw indexWord := by unfold inputSize;omega
  have hx := shift_le bits raw indexWord
  have hw := (metadata_bounds bits raw indexWord).2.2.2
  simp only [marked,List.length_cons,List.length_append,List.length_replicate]
  have hn : shiftCount bits raw indexWord-1 ≤ shiftCount bits raw indexWord := Nat.sub_le _ _
  nlinarith
/-- Generous common cap on every actual fit and all three real cleanup loops. -/
theorem finishTime_le (bits raw indexWord reader digit radix operand : List Bool)
    (hr : reader.length ≤ 200*(inputSize bits raw indexWord)^2)
    (hd : digit.length ≤ 200*(inputSize bits raw indexWord)^2)
    (ha : radix.length ≤ 200*(inputSize bits raw indexWord)^2)
    (ho : operand.length ≤ 200*(inputSize bits raw indexWord)^2) :
    finishTime (acquired bits raw indexWord) reader digit radix operand ≤ 10000*(inputSize bits raw indexWord)^2 := by
  have hs : 2 ≤ inputSize bits raw indexWord := by unfold inputSize;omega
  have he : (ellAt (acquired bits raw indexWord)).length ≤ inputSize bits raw indexWord :=
    (metadata_bounds bits raw indexWord).1
  have hf := fit_time_le operand (ellAt (acquired bits raw indexWord)++ellAt (acquired bits raw indexWord))
  simp only [List.length_append] at hf
  unfold finishTime
  nlinarith
/-- The actual branch clock includes all of the physical first/zero/one work. -/
theorem bodyBound_le (bits raw indexWord : List Bool) :
    bodyBound bits raw indexWord ≤ 1000000*(inputSize bits raw indexWord)^2 := by
  let s := inputSize bits raw indexWord
  have hs : 2 ≤ s := by dsimp [s,inputSize];omega
  have hr : raw.length ≤ s := by dsimp [s,inputSize];omega
  have hf := firstBound_le bits raw indexWord
  have hz : ([] : List Bool).length ≤ 200*s^2 := by simp
  have h1 : ([true] : List Bool).length ≤ 200*s^2 := by simp only [List.length_singleton];nlinarith
  have hzero := finishTime_le bits raw indexWord [] [] [] [] hz hz hz hz
  have hone := finishTime_le bits raw indexWord [] [] [] [true] hz hz hz h1
  have hrd : (suffix bits raw).length ≤ 200*s^2 := by
    have hh : (suffix bits raw).length ≤ raw.length := by rw [suffix,List.length_drop];omega
    nlinarith
  have hwd : (SemiprimeD1StackPublicInputMeaning.word bits raw).length ≤ 200*s^2 := by
    have hh := (metadata_bounds bits raw indexWord).2.2.2
    change _ ≤ 66*s at hh
    nlinarith
  have hra : (radixWord bits raw indexWord).length ≤ 200*s^2 := by
    have hh := (metadata_bounds bits raw indexWord).2.1
    change _ ≤ 66*s at hh
    nlinarith
  have hm := finishTime_le bits raw indexWord (suffix bits raw)
    (SemiprimeD1StackPublicInputMeaning.word bits raw) (radixWord bits raw indexWord)
    (marked (shiftCount bits raw indexWord) (SemiprimeD1StackPublicInputMeaning.word bits raw))
    hrd hwd hra (marked_length_le bits raw indexWord)
  have hsq : 1≤(inputSize bits raw indexWord)^2 := by dsimp only [s] at hs;nlinarith
  unfold bodyBound
  omega
/-- Fixed whole-program quadratic, chosen before every original input family. -/
def polynomial (bits raw indexWord : List Bool) : Nat :=
  1000000000000000*(inputSize bits raw indexWord)^2
/-- The whole own source budget derives from the actual52 checker plus actual new instructions. -/
theorem runBound_le (bits raw indexWord : List Bool) :
    runBound bits raw indexWord ≤ polynomial bits raw indexWord := by
  have hs : 2 ≤ inputSize bits raw indexWord := by unfold inputSize;omega
  have hbody := bodyBound_le bits raw indexWord
  unfold runBound SemiprimeD1StackPublicInputBounds.runBound polynomial
  change _ ≤ 1000000000000000*(inputSize bits raw indexWord)^2
  change bodyBound bits raw indexWord ≤ 1000000*(inputSize bits raw indexWord)^2 at hbody
  have hh : (inputSize bits raw indexWord)^2 ≥ 1 := by nlinarith
  dsimp only [inputSize] at hbody hh ⊢
  omega
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputCost

