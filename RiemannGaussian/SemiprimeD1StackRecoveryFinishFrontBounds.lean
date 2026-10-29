/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishOperatorBounds
import RiemannGaussian.SemiprimeD1StackRecoveryFinishPreparation
/-! # Own actual binary frontend and scalar-cache preparation clocks
Original binary numerator/denominator byte lengths, and actual WIDTH marker
bytes, pay all original copies, padding scans, floor work and cache acquisition.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishFrontBounds
open SemiprimeBitArithmetic
open SemiprimeBitIndexClipping (SignedWord)
namespace W
export SemiprimeD1StackRecoveryFinishWords (corrected dropped odd zeros zeros_le)
end W
namespace R
export SemiprimeD1StackRecoveryFinishRound (rawClock incrementTime roundTime)
end R
namespace B
export SemiprimeD1StackRecoveryFinishSetup (signedTape)
end B
namespace F
export SemiprimeD1StackRecoveryFinishFloor (floorTime)
end F
namespace P
export SemiprimeD1StackRecoveryFinishPreparation (floorBank oddBank twoBank oneBank time)
end P
namespace O
export SemiprimeD1StackRecoveryFinishOperatorBounds (cache_time)
end O
/-- Full real raw increment adds at most two physical output cells, including its literal carry cell. -/
theorem add_one_length (word:List Bool):(addBits word [true] false).bits.length≤ word.length+2:=by
  have h:=(addBits_counts word [true] false).2.2.2.2
  simp only [List.length_cons,List.length_nil,Nat.zero_add] at h
  have hm:max word.length 1≤ word.length+1:=max_le (by omega) (by omega)
  omega
/-- Exact actual raw-adder call clock has a linear physical-word bound. -/
theorem raw_clock (word:List Bool):R.rawClock word≤5*word.length+13:=by
  have h:=add_one_length word
  have hm:max word.length 1≤ word.length+1:=max_le (by omega) (by omega)
  unfold R.rawClock
  omega
/-- Actual source-consuming moves and raw increment retain a fixed linear byte clock. -/
theorem increment_time (word:List Bool):R.incrementTime word≤17*word.length+40:=by
  have hr:=raw_clock word
  have hl:=add_one_length word
  unfold R.incrementTime
  omega
/-- Finite actual sign/loss branches, including all raw increment/copy/drain returns, have a linear input-byte clock. -/
theorem round_time (negative lost:Bool) (word:List Bool):R.roundTime negative lost word≤100*(word.length+1):=by
  have h:=increment_time word
  cases negative <;> cases lost <;> simp only [R.roundTime,Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,ite_true] <;> omega
/-- Actual paired numerator shifts never create uncharged original magnitude bytes. -/
theorem dropped_length (d magnitude:List Bool):(W.dropped d magnitude).length≤ magnitude.length:=by
  simp only [W.dropped,List.length_drop]
  omega
/-- Actual raw floor correction has no supplied quotient/output bound; it follows from the original binary input. -/
theorem corrected_length (n:SignedWord) (d:List Bool):(W.corrected n.negative d n.magnitude).length≤(B.signedTape n).length+1:=by
  have hd:=dropped_length d n.magnitude
  have ha:=add_one_length (W.dropped d n.magnitude)
  have hn:(B.signedTape n).length=n.magnitude.length+1:=rfl
  unfold W.corrected
  split <;> omega
/-- SAME whole actual floor frontend is linear in original binary operand bytes, including arbitrary negative remainders. -/
theorem floor_time (n:SignedWord) (d:List Bool):F.floorTime n d≤1000*((B.signedTape n).length+d.length+1):=by
  have hz:=W.zeros_le d
  have hl:=dropped_length d n.magnitude
  have hr:=round_time n.negative (SemiprimeD1StackRecoveryFinishWords.lost d n.magnitude) (W.dropped d n.magnitude)
  have hn:(B.signedTape n).length=n.magnitude.length+1:=rfl
  unfold F.floorTime
  omega
/-- Actual copied odd suffix is bounded by its original binary denominator word, including padding. -/
theorem odd_length (d:List Bool):(W.odd d).length≤ d.length:=by
  simp only [W.odd,List.length_drop]
  omega
/-- SAME actual cache preparation pays all full input/high-padding scans and actual unary WIDTH markers. -/
theorem preparation_time (n:SignedWord) (d w:List Bool):P.time n d w≤1000*((B.signedTape n).length+d.length+w.length+1):=by
  have t0:=O.cache_time (P.floorBank n d w)
  change SemiprimeD1StackRecoveryFinishCache.time (P.floorBank n d w)≤
    100*((W.corrected n.negative d n.magnitude).length+w.length+1) at t0
  have t1:=O.cache_time (P.oddBank n d w)
  change SemiprimeD1StackRecoveryFinishCache.time (P.oddBank n d w)≤100*((W.odd d).length+w.length+1) at t1
  have t2:=O.cache_time (P.twoBank n d w)
  change SemiprimeD1StackRecoveryFinishCache.time (P.twoBank n d w)≤100*(2+w.length+1) at t2
  have t3:=O.cache_time (P.oneBank n d w)
  change SemiprimeD1StackRecoveryFinishCache.time (P.oneBank n d w)≤100*(1+w.length+1) at t3
  have hq:=corrected_length n d
  have hd:=odd_length d
  unfold P.time
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryFinishFrontBounds
