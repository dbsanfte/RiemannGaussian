/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersEncoding
/-! # Own physical successor costs from fitted scalar widths and actual history bytes
No later operand is bounded by an elapsed prefix clock. Every persistent current
is a real fitted scalar, except literal ONE, and every history byte is framed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersCost
open SemiprimeD1StackRecoveryPowers
open SemiprimeD1StackRecoveryPowersView hiding Stack
open SemiprimeD1StackRecoveryPowersSpec (signed row next suffix)
open SemiprimeD1StackRecoveryPowersEncoding
open SemiprimeD1StackRecoveryPowersOperationOutput
open SemiprimeRationalBits (RationalWord)
/-- Every actual word in a canonical loop store is bounded by actual metadata/history and fitted scalar bytes. -/
theorem loop_mass (argument current:RationalWord) (q n:Nat) (width hist:List Bool) (s:Nat)
    (hs:1 ≤ s) (ha:argument.numerator.magnitude.length ≤ s) (hd:argument.denominator.length ≤ s)
    (hq:q ≤ s) (hn:n ≤ s) (hw:width.length ≤ s)
    (hc:current.numerator.magnitude.length ≤ s) (hcd:current.denominator.length ≤ s) (hh:hist.length ≤ 10*s^2):
    SemiprimeD1StackRecoveryPowersCleanup.mass (bank (loopWords argument q width current n hist)) ≤ 1000*s^2:=by
  have hs2:s ≤ s^2:=Nat.le_pow (by decide:0<2)
  have hwords:∀slot:Stack,(bank (loopWords argument q width current n hist) slot).length ≤ 20*s^2:=by
    intro slot
    rcases slot with slot|slot
    · change (if slot=SemiprimeD1StackRationalOperation.aux .template then width else []).length ≤ 20*s^2
      split
      · omega
      · simp only [List.length_nil]
        omega
    · cases slot <;> simp only [bank,loopWords,Sum.elim_inr,signed,List.length_cons,List.length_replicate,List.length_nil] <;> omega
  have h:=SemiprimeD1StackRecoveryPowersOperation.word_sum _ _ hwords
  omega
/-- SAME real R36 call has fixed sixth-degree source-byte cost; argument values remain binary. -/
theorem rational_cost (argument current:RationalWord) (width:List Bool) (s:Nat)
    (hs:1 ≤ s) (ha:argument.numerator.magnitude.length ≤ s) (hd:argument.denominator.length ≤ s)
    (hw:width.length ≤ s) (hc:current.numerator.magnitude.length ≤ s) (hcd:current.denominator.length ≤ s):
    SemiprimeD1StackRationalOperationExecution.runBound .mul current.numerator.negative current.numerator.magnitude current.denominator
      argument.numerator.negative argument.numerator.magnitude argument.denominator width ≤ 10^27*s^6:=by
  have h:=SemiprimeD1StackRationalOperationBounds.runBound_le .mul current.numerator.negative current.numerator.magnitude current.denominator
    argument.numerator.negative argument.numerator.magnitude argument.denominator width
  have hi:SemiprimeD1StackRationalOperationEncoding.inputSize (signed current) current.denominator (signed argument) argument.denominator width ≤ 8*s:=by
    unfold SemiprimeD1StackRationalOperationEncoding.inputSize signed
    simp only [List.length_cons]
    omega
  have hp:=Nat.pow_le_pow_left hi 6
  unfold SemiprimeD1StackRationalOperationBounds.polynomial at h
  simp only [signed] at hp
  nlinarith only [h,hp]
/-- Prefix field copies, erased old current, actual sign and output acquisition are all charged from semantic fitted widths. -/
theorem prefix_cost (argument current:RationalWord) (q n:Nat) (width hist:List Bool) (s:Nat)
    (hs:1 ≤ s) (ha:argument.numerator.magnitude.length ≤ s) (hd:argument.denominator.length ≤ s)
    (hw:width.length ≤ s) (hc:current.numerator.magnitude.length ≤ s) (hcd:current.denominator.length ≤ s):
    SemiprimeD1StackRecoveryPowersOperation.prefixTime (loopWords argument q width current n hist)
      current.numerator.negative current.numerator.magnitude current.denominator
      argument.numerator.negative argument.numerator.magnitude argument.denominator width ≤ 10^28*s^6:=by
  have hr:=rational_cost argument current width s hs ha hd hw hc hcd
  have hl:=SemiprimeD1StackRationalOperationOriginal.output_lengths .mul current.numerator.negative current.numerator.magnitude current.denominator
    argument.numerator.negative argument.numerator.magnitude argument.denominator width
  have hs6:s ≤ s^6:=Nat.le_pow (by decide:0<6)
  change (word .mul current.numerator.negative current.numerator.magnitude current.denominator argument.numerator.negative
    argument.numerator.magnitude argument.denominator width).numerator.magnitude.length=width.length ∧
    (word .mul current.numerator.negative current.numerator.magnitude current.denominator argument.numerator.negative
    argument.numerator.magnitude argument.denominator width).denominator.length=width.length at hl
  unfold SemiprimeD1StackRecoveryPowersOperation.prefixTime SemiprimeD1StackRecoveryPowersOperationInput.inputsTime saveTime
  change 5*((signed current).length+current.denominator.length+(signed argument).length+argument.denominator.length)+16+_+_+_ ≤ _
  simp only [signed,List.length_cons,loopWords,hl.1,hl.2]
  omega
/-- Complete physical successor includes all35 real drains and every retained history byte. -/
theorem operation_cost (argument current:RationalWord) (q n:Nat) (width hist:List Bool) (s:Nat)
    (hs:1 ≤ s) (ha:argument.numerator.magnitude.length ≤ s) (hd:argument.denominator.length ≤ s)
    (hq:q ≤ s) (hn:n ≤ s) (hw:width.length ≤ s)
    (hc:current.numerator.magnitude.length ≤ s) (hcd:current.denominator.length ≤ s) (hh:hist.length ≤ 10*s^2):
    SemiprimeD1StackRecoveryPowersOperation.timeBound (loopWords argument q width current n hist)
      current.numerator.negative current.numerator.magnitude current.denominator
      argument.numerator.negative argument.numerator.magnitude argument.denominator width ≤ 10^33*s^6:=by
  have hm:=loop_mass argument current q n width hist s hs ha hd hq hn hw hc hcd hh
  have hp:=prefix_cost argument current q n width hist s hs ha hd hw hc hcd
  have hs6:1 ≤ s^6:=one_le_pow₀ hs
  have h26:s^2 ≤ s^6:=Nat.pow_le_pow_right hs (by decide:2 ≤ 6)
  unfold SemiprimeD1StackRecoveryPowersOperation.timeBound
  omega
/-- Actual persistent row width pays the literal sign/tag/delimiters, even W0 and literalONE. -/
theorem row_cap (current:RationalWord) (s:Nat) (hn:current.numerator.magnitude.length ≤ s) (hd:current.denominator.length ≤ s):
    (row current).length ≤ 4*s+5:=by
  rw [SemiprimeD1StackRecoveryPowersSpec.row_length]
  omega
/-- Complete source cache payload has linear row count and scalar width, without an output-size oracle. -/
theorem payload_cap (argument current:RationalWord) (width:List Bool) (n s:Nat)
    (hw:width.length ≤ s) (hc:current.numerator.magnitude.length ≤ s) (hd:current.denominator.length ≤ s):
    (payload (suffix width argument current n)).length ≤ n*(4*s+5):=by
  induction n generalizing current with
  | zero=>simp only [suffix,payload,List.flatMap_nil,List.length_nil,Nat.zero_mul,le_refl]
  | succ n ih=>
    have hn:=SemiprimeD1StackRecoveryPowersSpec.next_lengths width argument current
    have ht:=ih (next width argument current) (hn.1.le.trans hw) (hn.2.le.trans hw)
    have hr:=row_cap current s hc hd
    dsimp only [payload] at ht
    simp only [suffix,payload,List.flatMap_cons,List.length_append]
    nlinarith
end RiemannGaussian.SemiprimeD1StackRecoveryPowersCost
