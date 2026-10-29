/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseCopyBounds
import RiemannGaussian.SemiprimeD1StackCachePhaseFoldBound
import RiemannGaussian.SemiprimeD1StackCachePhaseRejected
/-! # Own whole238-role source clock in ONLY the actual four input bit lengths
Rank and precision VALUES are paid by the restored physical cache. No native
report, decoded dimension, child evaluator or selected-bank height is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseClock
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseExecution SemiprimeD1StackCachePhaseProjection
open SemiprimeD1StackCachePhaseInputBounds SemiprimeD1StackCachePhaseCopyBounds SemiprimeD1StackCachePhaseFoldBound
open SemiprimeD1StackJetFoldWords (Modes modeTape)
/-- One fixed polynomial, chosen before every original input, phase, cache and child tape. -/
def polynomial (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes) :Nat :=
  10^80*(inputSize banks i modes+1)^16
/-- The SAME actual accepted source pays all cache access/copies/fold/block/guard/halt work. -/
theorem timeBound_le (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) (hv:ValidCache banks[i.val] axes p q newP) :
    timeBound banks i axes p q newP modes ≤ polynomial banks i modes :=by
  have h1:inputSize banks i modes+1 ≤ (inputSize banks i modes+1)^16:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤ inputSize banks i modes+1) (by decide:1 ≤ 16)
  have h2:(inputSize banks i modes+1)^2 ≤ (inputSize banks i modes+1)^16:=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h13:(inputSize banks i modes+1)^13 ≤ (inputSize banks i modes+1)^16:=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hr0:=SemiprimeD1StackFreshBankRestoreBounds.runBound_le banks i
  change _ ≤ 1000*SemiprimeD1StackFreshBankRestoreBounds.inputSize banks i at hr0
  have hr:SemiprimeD1StackFreshBankRestoreExecution.runBound banks i ≤ 1000*(inputSize banks i modes+1)^16:=by
    unfold inputSize at h1 ⊢
    omega
  have hn:SemiprimeD1StackCachePhaseNewCache.newCopyTime (restored banks i) ≤ 1000000*(inputSize banks i modes+1)^16:=
    (newCopyTime_le banks i modes).trans (Nat.mul_le_mul_left _ h2)
  have ho:SemiprimeD1StackCachePhaseOldCache.oldCopyTime (restored banks i) (folded axes q newP modes) ≤
      10000000000*(inputSize banks i modes+1)^16:=
    (oldCopyTime_le banks i axes p q newP modes hv).trans (Nat.mul_le_mul_left _ h2)
  have hb:SemiprimeD1StackJetBlocksReady.readyBound axes.prod q (coefficients axes q newP modes) ≤
      1000000000000*(inputSize banks i modes+1)^16:=
    (blockBound_le banks i axes p q newP modes hv).trans (Nat.mul_le_mul_left _ h2)
  have hf:SemiprimeD1StackJetFoldBounds.runBound (q::axes) newP modes ≤ 10^70*(inputSize banks i modes+1)^16:=
    (foldBound_le banks i axes p q newP modes hv).trans (Nat.mul_le_mul_left _ h13)
  unfold timeBound polynomial
  norm_num only at hf ⊢
  omega
/-- Actual accepted whole four-input execution with a fixed polynomial in its OWN physical input lengths. -/
theorem source_run_bounded (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (hp:∀r∈axes,0<r) (p:List Bool) (q:Nat) (hq:0<q) (newP:List Bool) (modes:Modes)
    (hv:ValidCache banks[i.val] axes p q newP) :
    ∃t ≤ polynomial banks i modes,SemiprimeD1StackCalls.run program t (source banks i modes)=
      some (done banks i axes p q newP modes) :=by
  obtain ⟨t,ht,he⟩:=source_run banks i axes hp p q hq newP modes hv
  exact ⟨t,ht.trans (timeBound_le banks i axes p q newP modes hv),he⟩
/-- Actual rejected source has the SAME four-input bound, without a prepared-cache validity assumption. -/
theorem rejected_run_bounded (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes)
    (hg:banks[i.val] (Fresh.contextStack (Header.aux .valid))=[false]) :
    ∃t ≤ polynomial banks i modes,SemiprimeD1StackCalls.run program t (source banks i modes)=
      some (SemiprimeD1StackCachePhaseRejected.done banks i (modeTape modes)) :=by
  obtain ⟨t,ht,he⟩:=SemiprimeD1StackCachePhaseRejected.source_run banks i (modeTape modes) hg
  refine ⟨t,?_,he⟩
  have hr:=SemiprimeD1StackFreshBankRestoreBounds.runBound_le banks i
  change _ ≤ 1000*SemiprimeD1StackFreshBankRestoreBounds.inputSize banks i at hr
  have h1:inputSize banks i modes+1 ≤ (inputSize banks i modes+1)^16:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤ inputSize banks i modes+1) (by decide:1 ≤ 16)
  unfold polynomial
  norm_num only
  unfold inputSize at h1 ⊢
  omega
end RiemannGaussian.SemiprimeD1StackCachePhaseClock
