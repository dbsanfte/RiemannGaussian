/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformQueryBounds
/-! # Complete own transform transition budget from original input tapes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformBounds
open SemiprimeD1StackPublicTransformMetadata SemiprimeD1StackPublicTransformWords
open SemiprimeD1StackPublicTransformSetup SemiprimeD1StackPublicTransformGuards
open SemiprimeD1StackPublicTransformInventory SemiprimeD1StackPublicTransformQueryBounds
open SemiprimeBitArithmetic
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Entire physically executed loop, including every short-circuit cleanup. -/
theorem loop_le (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (hg : inputFlag (rootData bits) raw second=true) (n f : ℕ)
    (hn : n ≤ size bits second) (hf : f ≤ inputSize bits raw second inverse) :
    SemiprimeD1StackPublicTransformLoop.budget bits raw second inverse n f ≤
      (n+1)*(10^21*(inputSize bits raw second inverse)^16+30*inputSize bits raw second inverse+30) := by
  induction n generalizing f with
  | zero=>simp only [SemiprimeD1StackPublicTransformLoop.budget,Nat.zero_add,Nat.one_mul];omega
  | succ n ih=>
    have hsize:=(caps bits raw second inverse).2.2.2.2.2.1
    have hq:=query_le bits raw second inverse n hc hN hg (by omega)
    have hrec:=ih n (by omega) (by omega)
    simp only [SemiprimeD1StackPublicTransformLoop.budget]
    rw [Nat.add_mul,Nat.one_mul]
    omega
/-- Original root/source/count/cache copies are all explicitly retained. -/
theorem setup_le (bits raw : List Bool) (second inverse : Bool) :
    metadataBudget (rootData bits) second inverse+normalizationBudget (rootData bits) second inverse ≤
      200*inputSize bits raw second inverse := by
  obtain ⟨_,_,hm,hb,hNorm,hn,hs,hS⟩:=caps bits raw second inverse
  have hcount : (count bits second).length=size bits second := by
    rw [count_unary,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  have hstride : (count bits (!second)).length=size bits (!second) := by
    rw [count_unary,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  change (5*(baseCode bits inverse).length+4)+5*(5*(cached bits).length+4)+3*(5*(count bits second).length+4)+
    (5*(count bits (!second)).length+4)+normalizationBudget (rootData bits) second inverse ≤ _
  rw [hcount,hstride]
  unfold normalizationBudget
  split
  · rename_i hh
    rw [Bool.and_eq_true] at hh
    rcases hh with ⟨rfl,rfl⟩
    change (5*(baseCode bits true).length+4)+5*(5*(cached bits).length+4)+3*(5*size bits true+4)+
      (5*size bits (!true)+4)+(5*(normalizer bits true true).length+4) ≤ _
    omega
  · omega
/-- Both actual original vector acquisitions and all source copies are paid. -/
theorem words_le (bits raw : List Bool) (second inverse : Bool) :
    wordsBudget (rootData bits) raw second ≤ 3000*(inputSize bits raw second inverse)^2 := by
  let S:=inputSize bits raw second inverse
  obtain ⟨_,hr,hm,_,_,hn,_,hS⟩:=caps bits raw second inverse
  have hc : (countWord (rootData bits) second).length=size bits second := by
    change (count bits second).length=_
    rw [count_unary,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  have hraw : (outputRaw (rootData bits) raw second).length ≤ raw.length := by simp only [outputRaw,List.length_drop];omega
  unfold wordsBudget SemiprimeD1StackWordVectorExecution.timeBound
  rw [hc]
  change (5*raw.length+4)+(100*(raw.length+(size bits second+1)*((cached bits).length+1)+1)+1)+
    (5*(outputRaw (rootData bits) raw second).length+4)+
    (100*((outputRaw (rootData bits) raw second).length+(size bits second+1)*((cached bits).length+1)+1)+1) ≤ 3000*S^2
  have hmul:=Nat.mul_le_mul (show size bits second+1 ≤ S+1 by omega)
    (show (cached bits).length+1 ≤ S+1 by omega)
  change raw.length ≤ S at hr
  change (cached bits).length ≤ S at hm
  nlinarith
private theorem guard_poly (t v m S : ℕ) (ht : t ≤ 200*(v+m+1)^2)
    (hv : v ≤ 5*S^2) (hm : m ≤ S) (hs : 2 ≤ S) : t ≤ 10000*S^4 := by
  have hsum : v+m+1 ≤ 7*S^2 := by nlinarith
  have h:=Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hsum 2)
  rw [mul_pow,←pow_mul,←Nat.mul_assoc] at h
  norm_num only [Nat.reducePow,Nat.reduceMul] at h
  omega
/-- Computed input/output guards include physical full-vector copies and scans. -/
theorem front_le (bits raw : List Bool) (second inverse : Bool) :
    frontBudget (rootData bits) raw second ≤ 1000000*(inputSize bits raw second inverse)^4 := by
  let S:=inputSize bits raw second inverse
  obtain ⟨_,_,hm,_,_,hn,_,hS⟩:=caps bits raw second inverse
  obtain ⟨hvi,hvo⟩:=vector_caps bits raw second inverse
  have hi:=guard_poly _ _ _ _ (SemiprimeD1StackVectorCanonicalBounds.timeBound_le
    (inputs (rootData bits) raw second) (cached bits)) hvi hm hS
  have ho:=guard_poly _ _ _ _ (SemiprimeD1StackVectorCanonicalBounds.timeBound_le
    (outputs (rootData bits) raw second) (cached bits)) hvo hm hS
  have hc : (countWord (rootData bits) second).length=size bits second := by
    change (count bits second).length=_
    rw [count_unary,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  change (vectorBits (inputs (rootData bits) raw second)).length ≤ 5*S^2 at hvi
  change (vectorBits (outputs (rootData bits) raw second)).length ≤ 5*S^2 at hvo
  change SemiprimeD1StackVectorCanonicalExecution.timeBound (inputs (rootData bits) raw second)
    (modulusWord (rootData bits)) ≤ 10000*S^4 at hi
  change SemiprimeD1StackVectorCanonicalExecution.timeBound (outputs (rootData bits) raw second)
    (modulusWord (rootData bits)) ≤ 10000*S^4 at ho
  change size bits second ≤ S at hn
  have h2 : S^2 ≤ S^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : S ≤ S^4 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ S) (by decide : 1 ≤ 4)
  have hp : 0<S^4 := Nat.pow_pos (by omega)
  unfold frontBudget
  rw [hc]
  change _ ≤ 1000000*S^4
  omega
private theorem loop_poly (n S : ℕ) (hn : n ≤ S) (hs : 2 ≤ S) :
    (n+1)*(10^21*S^16+30*S+30) ≤ 10^24*S^18 := by
  have hlin : S ≤ S^16 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ S) (by decide : 1 ≤ 16)
  have hp : 0<S^16 := Nat.pow_pos (by omega)
  have hterm : 10^21*S^16+30*S+30 ≤ 10^22*S^16 := by norm_num only [Nat.reducePow];omega
  have h:=Nat.mul_le_mul (show n+1 ≤ 2*S by omega) hterm
  rw [show (2*S)*(10^22*S^16)=2*10^22*S^17 by ring] at h
  have hmono : S^17 ≤ S^18 := Nat.pow_le_pow_right (by omega) (by decide)
  norm_num only [Nat.reducePow,Nat.reduceMul] at h ⊢
  omega
/-- Entire actual source budget has a uniform fixed polynomial in original
acquired physical inventory. Failed guard branches do not pay imaginary queries. -/
theorem timeBound_le (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    SemiprimeD1StackPublicTransformTraceBudget.timeBound bits raw second inverse+1 ≤
      10^25*(inputSize bits raw second inverse)^18 := by
  let S:=inputSize bits raw second inverse
  obtain ⟨hb,_,_,_,_,hn,_,hS⟩:=caps bits raw second inverse
  have hsetup:=setup_le bits raw second inverse
  have hwords:=words_le bits raw second inverse
  have hfront:=front_le bits raw second inverse
  have hroot : SemiprimeD1StackRootSourceBounds.timeBound bits ≤ 40000000*S^2 := by
    have h:=Nat.mul_le_mul_left 10000000 (Nat.pow_le_pow_left (show bits.length+1 ≤ 2*S by omega) 2)
    rw [mul_pow,←Nat.mul_assoc] at h
    norm_num only [Nat.reducePow,Nat.reduceMul] at h
    exact h
  have h1 : S ≤ S^18 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ S) (by decide : 1 ≤ 18)
  have h2 : S^2 ≤ S^18 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : S^4 ≤ S^18 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp : 0<S^18 := Nat.pow_pos (by omega)
  change metadataBudget (rootData bits) second inverse+normalizationBudget (rootData bits) second inverse ≤ 200*S at hsetup
  change wordsBudget (rootData bits) raw second ≤ 3000*S^2 at hwords
  change frontBudget (rootData bits) raw second ≤ 1000000*S^4 at hfront
  cases ha : SemiprimeD1StackPublicTransformExecution.acceptedInputs bits raw second with
  | false=>
    unfold SemiprimeD1StackPublicTransformTraceBudget.timeBound
    simp only [ha,Bool.false_eq_true,ite_false]
    change _ ≤ 10^25*S^18
    norm_num only [Nat.reducePow]
    omega
  | true=>
    have hh:=ha
    change (inputFlag (rootData bits) raw second && outputFlag (rootData bits) raw second)=true at hh
    rw [Bool.and_eq_true] at hh
    have hl:=(loop_le bits raw second inverse hc hN hh.1 (size bits second) 0 le_rfl (Nat.zero_le _)).trans
      (loop_poly _ _ hn hS)
    change SemiprimeD1StackPublicTransformLoop.budget bits raw second inverse (size bits second) 0 ≤ 10^24*S^18 at hl
    unfold SemiprimeD1StackPublicTransformTraceBudget.timeBound
    simp only [ha,ite_true]
    change _ ≤ 10^25*S^18
    norm_num only [Nat.reducePow] at hl ⊢
    omega
/-- Only the actual original binary/raw tape lengths occur in the final bound. -/
def runBound (bits raw : List Bool) : ℕ := 10^90*(bits.length+raw.length+1)^18
/-- No acquired cache width, component clock, canonicality or source-size answer
is an input to this original-tape transition polynomial. -/
theorem runBound_le (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    SemiprimeD1StackPublicTransformTraceBudget.timeBound bits raw second inverse+1 ≤ runBound bits raw := by
  have h:=Nat.mul_le_mul_left (10^25) (Nat.pow_le_pow_left (inputSize_le bits raw second inverse) 18)
  rw [mul_pow,←Nat.mul_assoc] at h
  norm_num only [Nat.reducePow,Nat.reduceMul] at h
  have ht:=timeBound_le bits raw second inverse hc hN
  unfold runBound
  norm_num only [Nat.reducePow]
  omega
end RiemannGaussian.SemiprimeD1StackPublicTransformBounds
