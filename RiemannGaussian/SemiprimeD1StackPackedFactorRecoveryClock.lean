/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryWidths
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryStageCosts
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryMeaning
/-! # A fixed quartic physical-bit clock for the whole recovery source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryClock
open SemiprimeD1StackPackedFactorRecoveryEncoding SemiprimeD1StackPackedFactorRecoveryExecution
open SemiprimeD1StackPackedFactorRecoveryWidths SemiprimeD1StackPackedFactorRecoveryStageCosts
open SemiprimeBitArithmetic SemiprimeBitDivision
/-- Fixed before every N/scalar; every physical input padding bit is charged. -/
def polynomial (bits scalar : List Bool) : ℕ := 1000000000000000*(inputSize bits scalar)^4
/-- Numerical closure for the actual readout plus one actual binary SQ and all actual remaining stages. -/
theorem arithmetic_budget (R : ℕ) (hR : 1≤R) :
    1000000*R^2+100000000*(32*R+1)^4+10000*(32*R+1)^3+100≤1000000000000000*R^4 := by
  have h : 32*R+1≤33*R := by omega
  have h4:=Nat.pow_le_pow_left h 4
  have h3:=Nat.pow_le_pow_left h 3
  rw [mul_pow] at h4 h3
  have h2 : R^2≤R^4 := Nat.pow_le_pow_right hR (by decide : 2≤4)
  have h31 : R^3≤R^4 := Nat.pow_le_pow_right hR (by decide : 3≤4)
  have h1 : 1≤R^4 := by simpa only [one_pow] using Nat.pow_le_pow_left hR 4
  norm_num at h4 h3
  nlinarith only [h4,h3,h2,h31,h1]
/-- Square branch includes real source, parser, two copies, all physical validation and halt. -/
theorem square_le (bits scalar : List Bool) : squareBound bits scalar≤polynomial bits scalar := by
  let L:=limit bits scalar
  have hL : 2≤L := by dsimp [L,limit,inputSize];omega
  have hn : bits.length≤L := by dsimp [L,limit,inputSize];omega
  have hs : (sumWord bits scalar).length≤L := (sum_length bits scalar).trans hn
  have hp : (SemiprimeD1StackPackedFactorRecoveryValidation.productWord (sumWord bits scalar) (sumWord bits scalar)).length≤L := by
    have h:=square_length bits scalar
    change (squareWord (sumWord bits scalar)).length≤L
    dsimp [L,limit,inputSize]
    omega
  have hv:=validation_le L bits (sumWord bits scalar) (sumWord bits scalar) hL hn hs hs hp
  have hlin : L+1≤(L+1)^3 := Nat.le_self_pow (by decide : 3≠0) _
  have hmeta : SemiprimeD1StackPackedMomentReadoutCost.polynomial bits scalar=1000000*(inputSize bits scalar)^2 := rfl
  have h0 : squareBound bits scalar≤1000000*(inputSize bits scalar)^2+10000*(L+1)^3+100 := by
    unfold squareBound
    rw [hmeta]
    nlinarith
  have h1:=arithmetic_budget (inputSize bits scalar) (by unfold inputSize;omega)
  unfold polynomial
  dsimp [L,limit] at h0
  omega
/-- Distinct branch has the SAME fixed quartic clock, from actual byte-width bounds only. -/
theorem distinct_le (bits scalar lo hi : List Bool)
    (hlo : lo.length≤6*bits.length+6) (hhi : hi.length≤6*bits.length+7) :
    distinctBound bits scalar lo hi≤polynomial bits scalar := by
  let L:=limit bits scalar
  obtain ⟨hn,hs,hsq,hfour,hd,hroot,hl,hh,hsmall,hlarge,hproduct⟩:=all_widths_of_lengths bits scalar lo hi hlo hhi
  have hL : 2≤L := by dsimp [L,limit,inputSize];omega
  have h0:=discriminant_le L bits (sumWord bits scalar) hn hs hsq hfour hd
  have h1:=minus_le L (sumWord bits scalar) (rootWord bits (sumWord bits scalar)) lo hs hroot hl
  have h2:=plus_le L (sumWord bits scalar) (rootWord bits (sumWord bits scalar)) hi hs hroot hh
  have h3:=SemiprimeD1StackPackedFactorRecoveryCompaction.time_le lo
  have h4:=SemiprimeD1StackPackedFactorRecoveryCompaction.time_le hi
  have h5:=validation_le L bits (SemiprimeD1StackReduceExecution.trimReverse lo.reverse)
    (SemiprimeD1StackReduceExecution.trimReverse hi.reverse) hL hn hsmall hlarge hproduct
  have hlin : L+1≤(L+1)^3 := Nat.le_self_pow (by decide : 3≠0) _
  have hpow : ((discriminant bits (sumWord bits scalar)).length+1)^4≤(L+1)^4 :=
    Nat.pow_le_pow_left (by omega) 4
  have hmeta : SemiprimeD1StackPackedMomentReadoutCost.polynomial bits scalar=1000000*(inputSize bits scalar)^2 := rfl
  have htotal : distinctBound bits scalar lo hi≤1000000*(inputSize bits scalar)^2+
      100000000*(L+1)^4+10000*(L+1)^3+100 := by
    unfold distinctBound
    rw [hmeta]
    nlinarith
  exact htotal.trans (by simpa only [L,limit,polynomial] using arithmetic_budget (inputSize bits scalar) (by unfold inputSize;omega))
/-- Default tails remain linearly bounded even for arbitrary invalid/odd scalar channels. -/
theorem default_half_lengths (bits scalar : List Bool) :
    (SemiprimeD1StackPackedFactorRecoveryMeaning.lowerTail bits scalar).length≤6*bits.length+6 ∧
      (SemiprimeD1StackPackedFactorRecoveryMeaning.upperTail bits scalar).length≤6*bits.length+7 := by
  have hs:=sum_length bits scalar
  have hr:=root_length bits scalar
  have hm : max (sumWord bits scalar).length (rootWord bits (sumWord bits scalar)).length≤6*bits.length+6 :=
    max_le (by omega) hr
  have h0:=(subBits_counts (sumWord bits scalar) (rootWord bits (sumWord bits scalar)) false).2.2.2.2
  have h1:=(addBits_counts (sumWord bits scalar) (rootWord bits (sumWord bits scalar)) false).2.2.2.2
  have h2 : ((minusReport (sumWord bits scalar) (rootWord bits (sumWord bits scalar))).result.bits.tail).length≤
      (minusReport (sumWord bits scalar) (rootWord bits (sumWord bits scalar))).result.bits.length := by
    simp only [List.length_tail];omega
  have h3 : (plusWord (sumWord bits scalar) (rootWord bits (sumWord bits scalar))).tail.length≤
      (plusWord (sumWord bits scalar) (rootWord bits (sumWord bits scalar))).length := by
    simp only [List.length_tail];omega
  change _≤(subBits _ _ false).result.bits.length at h2
  change _≤(addBits _ _ false).bits.length at h3
  unfold SemiprimeD1StackPackedFactorRecoveryMeaning.lowerTail SemiprimeD1StackPackedFactorRecoveryMeaning.upperTail
  omega
/-- Both actual accepted branches fit one fixed polynomial in the two physical input lengths. -/
theorem timeBound_le (bits scalar : List Bool) :
    SemiprimeD1StackPackedFactorRecoveryMeaning.timeBound bits scalar≤polynomial bits scalar := by
  unfold SemiprimeD1StackPackedFactorRecoveryMeaning.timeBound
  split_ifs
  · exact square_le bits scalar
  · obtain ⟨hl,hh⟩:=default_half_lengths bits scalar
    exact distinct_le bits scalar _ _ hl hh
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryClock
