/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedMomentReadoutStorage
import RiemannGaussian.SemiprimeD1PackedMomentSemiprime
import RiemannGaussian.SemiprimeD1CanonicalInput
/-! # Actual packed scalar yields count and factor sum for EVERY semiprime
The scalar is still an actual second prepared word, and its acquisition must
be joined by the original-N-only recursive counter. The moment outputs,
digit width, indices and all intermediate values are acquired by real code.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedMomentReadoutOriginal
open scoped BigOperators
open SemiprimeD1StackPackedMomentReadout SemiprimeD1StackPackedMomentReadoutEncoding
open SemiprimeD1StackPackedMomentReadoutExecution SemiprimeD1StackPackedMomentReadoutCost
open SemiprimeD1StackPackedMomentReadoutStorage
open SemiprimeBitArithmetic SemiprimeSourceCompactBits
namespace P
export SemiprimeD1PackedMomentSemiprime (packedValue readout moments moments_below_base)
end P
/-- Every actually acquired metadata word is retained without reacquisition or reinterpretation. -/
theorem metadata_retained (bits scalar : List Bool) (k : M.Stack) :
    (done bits scalar).data (metadata k)=metadataResult bits k := rfl
/-- Both actual original input words survive the two real extraction calls. -/
theorem inputs_retained (bits scalar : List Bool) :
    (done bits scalar).data originalInput=bits ∧ (done bits scalar).data scalarInput=scalar := ⟨rfl,rfl⟩
/-- All six actual radix source/work words are physically empty at halt. -/
theorem radix_empty (bits scalar : List Bool) (k : D.Stack) : (done bits scalar).data (digit k)=[] := rfl
/-- Both actually acquired moment outputs have compact byte encodings. -/
theorem outputs_compact (bits scalar : List Bool) :
    Compact ((done bits scalar).data (aux .count)) ∧ Compact ((done bits scalar).data (aux .sum)) :=
  ⟨moment_compact bits scalar false,moment_compact bits scalar true⟩
/-- Canonical original N identifies the actual acquired low-block width internally. -/
theorem output_count_value (bits scalar : List Bool) (hc : Compact bits) :
    bitValue ((done bits scalar).data (aux .count))=
      bitValue scalar%2^SemiprimeMacroParameters.bitLength (bitValue bits) := by
  change bitValue (moment bits scalar false)=_
  rw [count_value,SemiprimeD1CanonicalInput.compact_length bits hc]
/-- Canonical original N identifies the actual physically skipped high block. -/
theorem output_sum_value (bits scalar : List Bool) (hc : Compact bits) :
    bitValue ((done bits scalar).data (aux .sum))=
      (bitValue scalar/2^SemiprimeMacroParameters.bitLength (bitValue bits))%
        2^SemiprimeMacroParameters.bitLength (bitValue bits) := by
  change bitValue (moment bits scalar true)=_
  rw [sum_value,SemiprimeD1CanonicalInput.compact_length bits hc]
/-- Exact semiprime count and factor sum, with no local/global coverage premise or factor advice to runtime. -/
theorem semiprime_values (bits scalar : List Bool) (hc : Compact bits) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=P.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    bitValue ((done bits scalar).data (aux .count))=(if p=q then 1 else 2) ∧
      bitValue ((done bits scalar).data (aux .sum))=(if p=q then p else p+q) := by
  have h:=P.readout p q hp hq
  have hb : (if p=q then p else p+q) < 2^SemiprimeMacroParameters.bitLength (p*q) := by
    simpa only [(P.moments p q hp hq).2] using (P.moments_below_base p q hp hq).2
  constructor
  · rw [output_count_value bits scalar hc,hN,hscalar]
    exact h.1
  · rw [output_sum_value bits scalar hc,hN,hscalar,h.2,Nat.mod_eq_of_lt hb]
/-- The actual compact count bytes are literal1 or2, sufficient for a finite physical branch. -/
theorem semiprime_count_bytes (bits scalar : List Bool) (hc : Compact bits) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=P.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    (done bits scalar).data (aux .count)=(if p=q then [true] else [false,true]) := by
  have hv:=(semiprime_values bits scalar hc p q hp hq hN hscalar).1
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ (outputs_compact bits scalar).1
  · split_ifs <;> simp [Compact]
  · split_ifs with he
    · simpa [he,bitValue,bitNat] using hv
    · simpa [he,bitValue,bitNat] using hv
/-- Any actual compact packed-root scalar has a semantic2ell byte cap; no unary base is materialized. -/
theorem scalar_length (bits scalar : List Bool) (hc : Compact bits) (hcs : Compact scalar)
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=P.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    scalar.length ≤ 2*bits.length := by
  apply compact_length_of_lt scalar hcs
  rw [SemiprimeD1CanonicalInput.compact_length bits hc,hN,hscalar]
  unfold P.packedValue
  have : NeZero ((2^SemiprimeMacroParameters.bitLength (p*q))^2) := ⟨by positivity⟩
  have h:=ZMod.val_lt
    (SemiprimeD1PackedMomentOriginal.contraction (SemiprimePublicFactorCount.publicConfig (p*q) (Nat.mul_pos hp.pos hq.pos))
      ((2^SemiprimeMacroParameters.bitLength (p*q) : ℕ) : ZMod ((2^SemiprimeMacroParameters.bitLength (p*q))^2)))
  simpa only [←pow_mul,Nat.mul_comm (SemiprimeMacroParameters.bitLength (p*q)) 2] using h
/-- SAME actual source: whole-family count/sum acquisition from a real compact scalar, quadratic in original input bits. -/
theorem source_semiprime (bits scalar : List Bool) (hc : Compact bits) (hcs : Compact scalar)
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=P.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    ∃t ≤ 10000000*(bits.length+1)^2,
      SemiprimeD1StackCalls.run program t (initial bits scalar)=some (done bits scalar) ∧
      bitValue ((done bits scalar).data (aux .count))=(if p=q then 1 else 2) ∧
      bitValue ((done bits scalar).data (aux .sum))=(if p=q then p else p+q) := by
  have hl:=scalar_length bits scalar hc hcs p q hp hq hN hscalar
  have hw:=Nat.pow_le_pow_left (show bits.length+scalar.length+1 ≤ 3*(bits.length+1) by omega) 2
  obtain ⟨t,ht,hr⟩:=source_run_bounded bits scalar
  have hpw : polynomial bits scalar ≤ 10000000*(bits.length+1)^2 := by
    unfold polynomial
    nlinarith
  exact ⟨t,ht.trans hpw,hr,(semiprime_values bits scalar hc p q hp hq hN hscalar).1,
    (semiprime_values bits scalar hc p q hp hq hN hscalar).2⟩
/-- Actual finite prepared machine with the SAME quadratic clock, charging both physical inputs. -/
noncomputable def machinePrepared (bits scalar : List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial bits scalar))
      (some (SemiprimeD1StackCalls.configuration (done bits scalar))) (polynomial bits scalar) := by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput (aux .sum) (ctl .start) program
  let h:=source_run_bounded bits scalar
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackPackedMomentReadoutOriginal
