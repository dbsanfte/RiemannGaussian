/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBinarySquareRootLoop
/-! # Fixed bit-length cost of the SAME actual binary square-root loop
All candidate widths are controlled by raw-word semantics, independently of the
elapsed loop clock. Every copy, square, comparison and private erasure is paid.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRootCost
open SemiprimeD1StackBinarySquareRoot SemiprimeD1StackBinarySquareRootEncoding
open SemiprimeD1StackBinarySquareRootPrimitives SemiprimeD1StackBinarySquareRootCalls
open SemiprimeD1StackBinarySquareRootSweep SemiprimeD1StackBinarySquareRootDecision
open SemiprimeD1StackBinarySquareRootLoop SemiprimeD1StackBinarySquareRootArithmetic
open SemiprimeD1StackPackedRootMetadataEncoding (baseWord base_length)
/-- Cubic actual multiplier clock is retained, despite the sharper semantic output width. -/
theorem multiplyTime_le (a : List Bool) : multiplyTime a a ≤ 1000*(a.length+1)^3 := by
  have h:=Nat.add_le_add_right (SemiprimeD1StackMultiplierExecution.source_time a a) 1
  change multiplyTime a a ≤ SemiprimeD1StackMultiplierExecution.timeBound a.length a.length+1 at h
  apply h.trans
  unfold SemiprimeD1StackMultiplierExecution.timeBound
  ring_nf
  omega
/-- Private-bank cap uses the two actually live work words, never the root/metadata values. -/
theorem selected_private_length (bits p r newRoot : List Bool) (cap : ℕ)
    (ht : (E.trial r p).length ≤ cap) (hs : (E.square r p).length ≤ cap) :
    ∀i,(selected bits p r newRoot (clearStack i)).length ≤ cap := by
  intro i
  fin_cases i <;> first | exact ht | exact hs | exact Nat.zero_le _
/-- Actual copies, adder, square and comparison fit a fixed cubic in raw operand widths. -/
theorem testTime_le (bits p r : List Bool) (cap : ℕ)
    (hd : bits.length ≤ cap) (hp : p.length ≤ cap) (hr : r.length ≤ cap) :
    testTime bits p r ≤ 2000*(cap+2)^3 := by
  have ht : (E.trial r p).length ≤ cap+1 :=
    (trial_length r p).trans (Nat.add_le_add_right (max_le hr hp) 1)
  have hs : (E.square r p).length ≤ 3*(cap+1) := (square_length r p).trans (Nat.mul_le_mul_left 3 ht)
  have hm:=(multiplyTime_le (E.trial r p)).trans
    (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (show (E.trial r p).length+1 ≤ cap+2 by omega) 3))
  have hc:=SemiprimeD1StackWordLessExecution.totalTime_le bits (E.square r p)
  have hmax : max r.length p.length ≤ cap := max_le hr hp
  have hb : testTime bits p r ≤ 1000*(cap+2)^3+70*(cap+2) := by
    unfold testTime addTime compareTime
    omega
  apply hb.trans
  ring_nf
  omega
/-- Branch-specific erasure/copy is linear in the actual old/trial root widths. -/
theorem decisionTime_le (bits p r : List Bool) (cap : ℕ) (hp : p.length ≤ cap) (hr : r.length ≤ cap) :
    decisionTime bits p r ≤ 10*(cap+2) := by
  have ht : (E.trial r p).length ≤ cap+1 :=
    (trial_length r p).trans (Nat.add_le_add_right (max_le hr hp) 1)
  unfold decisionTime
  split_ifs <;> omega
/-- One complete actual bit test plus its physical power shift is uniformly cubic. -/
theorem iterationTime_le (bits p r : List Bool) (cap : ℕ)
    (hd : bits.length ≤ cap) (hp : p.length ≤ cap) (hr : r.length ≤ cap) :
    iterationTime bits p r+1 ≤ 4000*(cap+2)^3 := by
  have ht : (E.trial r p).length ≤ cap+1 :=
    (trial_length r p).trans (Nat.add_le_add_right (max_le hr hp) 1)
  have hs : (E.square r p).length ≤ 3*(cap+1) := (square_length r p).trans (Nat.mul_le_mul_left 3 ht)
  have hprivate:=selected_private_length bits p r (E.nextWord bits r p) (3*(cap+1)) (by omega) hs
  have hw:=sweepTime_le (selected bits p r (E.nextWord bits r p)) (3*(cap+1)) 18 hprivate
  have h0:=testTime_le bits p r cap hd hp hr
  have h1:=decisionTime_le bits p r cap hp hr
  have hb : iterationTime bits p r+1 ≤ 2000*(cap+2)^3+64*cap+93 := by
    unfold iterationTime
    omega
  apply hb.trans
  ring_nf
  omega
/-- The semantic width reserve decreases after each candidate-bit iteration. -/
theorem next_reserve (bits r : List Bool) (n cap : ℕ)
    (h : max r.length (n+2)+(n+2) ≤ cap) :
    max (E.nextWord bits r (baseWord (n+1))).length (n+1)+(n+1) ≤ cap := by
  have hg:=nextWord_length bits r (baseWord (n+1))
  rw [base_length] at hg
  have hm : max (E.nextWord bits r (baseWord (n+1))).length (n+1) ≤ max r.length (n+2)+1 :=
    max_le (by omega) (by omega)
  omega
/-- Whole n+1-test elapsed time: bit-length iteration count and fixed semantic width cap. -/
theorem loopTime_le (bits r : List Bool) (n cap : ℕ) (hd : bits.length ≤ cap)
    (hw : max r.length (n+1)+(n+1) ≤ cap) :
    loopTime bits n r ≤ (n+1)*(4000*(cap+2)^3) := by
  induction n generalizing r with
  | zero =>
    have hp : (baseWord 0).length ≤ cap := by rw [base_length];omega
    have hr : r.length ≤ cap := by have h:=le_max_left r.length 1;omega
    have hi:=iterationTime_le bits (baseWord 0) r cap hd hp hr
    simpa only [loopTime,Nat.zero_add,Nat.one_mul] using hi
  | succ n ih =>
    have hp : (baseWord (n+1)).length ≤ cap := by rw [base_length];omega
    have hr : r.length ≤ cap := (le_max_left r.length (n+1+1)).trans (by omega)
    have hi:=iterationTime_le bits (baseWord (n+1)) r cap hd hp hr
    have hn:=ih (E.nextWord bits r (baseWord (n+1))) (next_reserve bits r n cap hw)
    rw [loopTime]
    nlinarith
/-- Original input needs only a fixed linear semantic width reserve. -/
theorem original_loopTime_le (bits : List Bool) :
    loopTime bits bits.length [] ≤ (bits.length+1)*(4000*(2*(bits.length+1)+2)^3) := by
  apply loopTime_le bits [] bits.length (2*(bits.length+1)) (by omega)
  simp only [List.length_nil,max_eq_right (Nat.zero_le _)]
  omega
end RiemannGaussian.SemiprimeD1StackBinarySquareRootCost
