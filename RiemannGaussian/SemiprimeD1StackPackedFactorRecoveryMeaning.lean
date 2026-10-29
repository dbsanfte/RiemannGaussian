/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryExecution
/-! # Every semiprime discharges the actual recovery branches and physical checks
The prime factors occur only in proofs connecting the actual packed scalar
and actual output words. The runtime ABI remains original binary N plus V.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryMeaning
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackPackedFactorRecoveryExecution SemiprimeD1StackPackedFactorRecoveryArithmetic
open SemiprimeBitArithmetic SemiprimeSourceCompactBits
namespace O
export SemiprimeD1StackPackedMomentReadoutOriginal (semiprime_values semiprime_count_bytes)
end O
/-- Proof-only physical count-word case; the program executes its own byte parser. -/
abbrev squareCase (bits scalar : List Bool) : Prop := (retained bits scalar) (R.aux .count)=[true]
/-- The lower raw half is the actual physical low-bit-pop tail. -/
def lowerTail (bits scalar : List Bool) : List Bool :=
  (minusReport (sumWord bits scalar) (rootWord bits (sumWord bits scalar))).result.bits.tail
/-- The upper raw half is the actual physical low-bit-pop tail. -/
def upperTail (bits scalar : List Bool) : List Bool :=
  (plusWord (sumWord bits scalar) (rootWord bits (sumWord bits scalar))).tail
/-- Exact source result is specified from the actual readout/arithmetic words only. -/
def result (bits scalar : List Bool) : Stack→List Bool :=
  if squareCase bits scalar then squareResult bits scalar else distinctResult bits scalar (lowerTail bits scalar) (upperTail bits scalar)
/-- Own complete source bound uses the SAME actual branch's computed word lengths. -/
def timeBound (bits scalar : List Bool) : ℕ :=
  if squareCase bits scalar then squareBound bits scalar else distinctBound bits scalar (lowerTail bits scalar) (upperTail bits scalar)
/-- Full actual halt specification, with no erased foreign bank or saved return. -/
def done (bits scalar : List Bool) : C.State Stack Label := stopped (result bits scalar)
/-- Actual output bytes are compact in both source branches. -/
theorem outputs_compact (bits scalar : List Bool) :
    Compact ((done bits scalar).data (aux .small)) ∧ Compact ((done bits scalar).data (aux .large)) := by
  unfold done result
  split_ifs
  · exact ⟨SemiprimeD1StackPackedMomentReadoutEncoding.moment_compact bits scalar true,
      SemiprimeD1StackPackedMomentReadoutEncoding.moment_compact bits scalar true⟩
  · exact ⟨SemiprimeD1StackReduceExecution.trimReverse_compact _,SemiprimeD1StackReduceExecution.trimReverse_compact _⟩
/-- Every readout word, including all actual metadata/scalar/count/sum and six empty radix roles, is retained. -/
theorem readout_retained (bits scalar : List Bool) (k : R.Stack) :
    (done bits scalar).data (readout k)=retained bits scalar k := by unfold done result;split_ifs <;> rfl
/-- The actual TRUE singleton is written only after the real common validation path. -/
theorem status_true (bits scalar : List Bool) : (done bits scalar).data (aux .status)=[true] := by
  unfold done result;split_ifs <;> rfl
/-- Complete SAME source computes the ordered two factors for EVERY ordered semiprime pair. -/
theorem source_ordered (bits scalar : List Bool) (hc : Compact bits) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p≤q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    ∃t ≤ timeBound bits scalar,
      SemiprimeD1StackCalls.run program t (initial bits scalar)=some (done bits scalar) ∧
      bitValue ((done bits scalar).data (aux .small))=p ∧ bitValue ((done bits scalar).data (aux .large))=q := by
  have hcount:=O.semiprime_count_bytes bits scalar hc p q hp hq hN hscalar
  have hsum:=(O.semiprime_values bits scalar hc p q hp hq hN hscalar).2
  change bitValue (sumWord bits scalar)=(if p=q then p else p+q) at hsum
  change (retained bits scalar) (R.aux .count)=(if p=q then [true] else [false,true]) at hcount
  by_cases he:p=q
  · subst q
    rw [ite_eq_left rfl] at hcount hsum
    obtain ⟨t,ht,hr⟩:=square_run bits scalar hcount (by rw [hsum];exact hp.two_le) (by rw [hsum,hN])
    have hsquare : squareCase bits scalar := hcount
    refine ⟨t,?_,?_,?_,?_⟩
    · simpa only [timeBound,ite_eq_left hsquare] using ht
    · simpa only [done,result,ite_eq_left hsquare] using hr
    · change bitValue ((if squareCase bits scalar then squareResult bits scalar else _) (aux .small))=p
      rw [ite_eq_left hsquare]
      exact hsum
    · change bitValue ((if squareCase bits scalar then squareResult bits scalar else _) (aux .large))=p
      rw [ite_eq_left hsquare]
      exact hsum
  · rw [ite_eq_right he] at hcount hsum
    have hsquare : ¬squareCase bits scalar := by
      intro h
      have hh:=h.symm.trans hcount
      cases hh
    let s:=sumWord bits scalar
    let root:=rootWord bits s
    have hd:=discriminant_borrow bits s p q hN hsum
    have hroot:=rootWord_value bits s p q hN hsum hpq
    obtain ⟨hm,⟨lo,hlo⟩,hvlo⟩:=minus_exact s root p q hp.pos hpq hsum hroot
    obtain ⟨⟨hi,hhi⟩,hvhi⟩:=plus_exact s root p q hq.pos hpq hsum hroot
    have hsmall : bitValue (SemiprimeD1StackReduceExecution.trimReverse lo.reverse)=p := by
      simpa only [halfWord,hlo,List.tail_cons] using hvlo
    have hlarge : bitValue (SemiprimeD1StackReduceExecution.trimReverse hi.reverse)=q := by
      simpa only [halfWord,hhi,List.tail_cons] using hvhi
    have hlower : lowerTail bits scalar=lo := by change (minusReport s root).result.bits.tail=lo;rw [hlo];rfl
    have hupper : upperTail bits scalar=hi := by change (plusWord s root).tail=hi;rw [hhi];rfl
    obtain ⟨t,ht,hr⟩:=distinct_run bits scalar lo hi hcount hd hm hlo hhi
      (by rw [hsmall];exact hp.two_le) (by rw [hlarge];exact hq.two_le) (by rw [hsmall,hlarge,hN])
    refine ⟨t,?_,?_,?_,?_⟩
    · simpa only [timeBound,ite_eq_right hsquare,hlower,hupper] using ht
    · simpa only [done,result,ite_eq_right hsquare,hlower,hupper] using hr
    · change bitValue ((if squareCase bits scalar then _ else distinctResult bits scalar (lowerTail bits scalar) (upperTail bits scalar)) (aux .small))=p
      rw [ite_eq_right hsquare,hlower,hupper]
      exact hsmall
    · change bitValue ((if squareCase bits scalar then _ else distinctResult bits scalar (lowerTail bits scalar) (upperTail bits scalar)) (aux .large))=q
      rw [ite_eq_right hsquare,hlower,hupper]
      exact hlarge
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryMeaning
