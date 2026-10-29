/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedMomentReadoutExecution
/-! # Own quadratic bit cost; actual scalar and N bytes are charged separately -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedMomentReadoutCost
open SemiprimeD1StackPackedMomentReadout SemiprimeD1StackPackedMomentReadoutEncoding
open SemiprimeD1StackPackedMomentReadoutPrimitives SemiprimeD1StackPackedMomentReadoutBlock
open SemiprimeD1StackPackedMomentReadoutExecution
/-- Actual radix budget with literal index0/1 is linear in N width and scalar bytes. -/
theorem digitTime_le (bits scalar : List Bool) (high : Bool) :
    digitTime bits scalar high ≤ 18*bits.length+5*scalar.length+25 := by
  have h:=SemiprimeD1StackRadixDigitExecution.totalTime_le scalar (width bits) (index high)
  unfold digitTime SemiprimeD1StackRadixDigitExecution.timeBound at *
  cases high <;> simp only [width,index,Bool.false_eq_true,ite_false,ite_true,List.length_nil,
    List.length_singleton,List.length_replicate,Nat.mul_zero,Nat.mul_one,Nat.zero_add] at * <;> omega
/-- Every actual block pays all width/value/output copies and full output erasure. -/
theorem blockTime_le (bits scalar : List Bool) (high : Bool) :
    blockTime bits scalar high ≤ 100*(bits.length+scalar.length+1) := by
  have hd:=digitTime_le bits scalar high
  have hm:=moment_length bits scalar high
  have hs : seedTime high ≤ 1 := by cases high <;> decide
  unfold blockTime saveTime
  simp only [width,List.length_replicate]
  omega
/-- Actual acquired-cache continuation is linear in both actual input-word lengths. -/
theorem readyBound_le (bits scalar : List Bool) :
    readyBound bits scalar ≤ 300*(bits.length+scalar.length+1) := by
  have h0:=blockTime_le bits scalar false
  have h1:=blockTime_le bits scalar true
  unfold readyBound
  omega
/-- Whole-source fixed polynomial includes actual N-width acquisition and all scalar reads. -/
def polynomial (bits scalar : List Bool) : ℕ := 1000000*(bits.length+scalar.length+1)^2
/-- Same-cache continuation has its OWN linear budget. -/
def readyPolynomial (bits scalar : List Bool) : ℕ := 300*(bits.length+scalar.length+1)
/-- Actual whole-source elapsed bound is quadratic in the actual two-word input size. -/
theorem runBound_le (bits scalar : List Bool) : runBound bits scalar ≤ polynomial bits scalar := by
  have hr:=readyBound_le bits scalar
  have hN:=Nat.pow_le_pow_left (show bits.length+1 ≤ bits.length+scalar.length+1 by omega) 2
  have hR : bits.length+scalar.length+1 ≤ (bits.length+scalar.length+1)^2 := Nat.le_pow (by decide : 0<(2:ℕ))
  unfold runBound polynomial SemiprimeD1StackPackedRootMetadataExecution.polynomial
  omega
/-- Actual whole two-word source has the proved fixed quadratic clock. -/
theorem source_run_bounded (bits scalar : List Bool) :
    ∃t ≤ polynomial bits scalar,SemiprimeD1StackCalls.run program t (initial bits scalar)=some (done bits scalar) := by
  obtain ⟨t,ht,h⟩:=source_run bits scalar
  exact ⟨t,ht.trans (runBound_le bits scalar),h⟩
/-- SAME actual N-width-cache source has a linear clock without re-acquiring metadata. -/
theorem ready_run_bounded (bits scalar : List Bool) :
    ∃t ≤ readyPolynomial bits scalar,SemiprimeD1StackCalls.run program t (ready bits scalar)=some (done bits scalar) := by
  obtain ⟨t,ht,h⟩:=ready_run bits scalar
  exact ⟨t,ht.trans (readyBound_le bits scalar),h⟩
end RiemannGaussian.SemiprimeD1StackPackedMomentReadoutCost
