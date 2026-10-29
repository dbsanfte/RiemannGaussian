/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicZeroBounds
import RiemannGaussian.SemiprimeMacroEntryBitCheck

/-! # Both original carry endpoints on every finite assignment
Actual original-N width acquisition and raw-block extraction are paid by this
same checker. Their verdict is EXACT publicBitEntry for initial/terminal carry,
without a supplied word, width, zero/nonzero predicate or old report clock.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPublicZeroOriginal
open SemiprimeD1StackPublicZero SemiprimeD1StackPublicZeroExecution SemiprimeD1StackPublicZeroBounds
open SemiprimeMacroGraph SemiprimeMacroEntryBitCheck SemiprimeMacroEntryBitPrimitives
open SemiprimeMacroParameters SemiprimeBitArithmetic
/-- Actual acquired width equals the original public carry-word arity. -/
theorem public_width (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    (cached bits).length=firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1 := by
  rw [cached_length,SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc,axes_product]
/-- Complete raw words are returned with all original zero padding unchanged. -/
theorem word_full (bits raw : List Bool) (hw : raw.length=(cached bits).length) : word bits raw=raw := by
  unfold word
  rw [SemiprimeD1StackWordBlockExecution.result_take raw (cached bits) (by omega)]
  exact List.take_of_length_le (by omega)
/-- ALL original carry-initial assignments, exact original checker verdict. -/
theorem initial_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (input : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)→Bool) :
    answer bits (List.ofFn input)=(publicBitEntry (bitValue bits) hN .carryInitial input).accepted := by
  let p:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
  have hp:=publicBitEntry_correct (bitValue bits) hN .carryInitial input
  have he:=entryRun_correct p (configTargets p) .carryInitial input
  have hz : answer bits (List.ofFn input)=(entryRun p (configTargets p) .carryInitial input).accepted := by
    apply Bool.eq_iff_iff.mpr
    change decide (bitValue (word bits (List.ofFn input))=0)=true ↔
      (equalBits (List.ofFn input) []).accepted=true
    rw [decide_eq_true_eq,equalBits_correct,word_full bits (List.ofFn input) (by rw [List.length_ofFn,public_width bits hc])]
    rfl
  exact hz.trans (he.trans hp.symm)
/-- ALL original carry-terminal assignments, exact original checker verdict. -/
theorem terminal_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (input : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)→Bool) :
    answer bits (List.ofFn input)=(publicBitEntry (bitValue bits) hN .carryTerminal input).accepted := by
  let p:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
  have hp:=publicBitEntry_correct (bitValue bits) hN .carryTerminal input
  have he:=entryRun_correct p (configTargets p) .carryTerminal input
  have hz : answer bits (List.ofFn input)=(entryRun p (configTargets p) .carryTerminal input).accepted := by
    apply Bool.eq_iff_iff.mpr
    change decide (bitValue (word bits (List.ofFn input))=0)=true ↔
      (equalBits (List.ofFn input) []).accepted=true
    rw [decide_eq_true_eq,equalBits_correct,word_full bits (List.ofFn input) (by rw [List.length_ofFn,public_width bits hc])]
    rfl
  exact hz.trans (he.trans hp.symm)
/-- Literal actual output singleton is the old initial carry result. -/
theorem initial_output (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (input : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)→Bool) :
    (done bits (List.ofFn input)).data output=[(publicBitEntry (bitValue bits) hN .carryInitial input).accepted] := by
  change [answer bits (List.ofFn input)]=_
  exact congrArg (fun b : Bool=>[b]) (initial_original bits hc hN input)
/-- Literal actual output singleton is the old terminal carry result. -/
theorem terminal_output (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (input : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)→Bool) :
    (done bits (List.ofFn input)).data output=[(publicBitEntry (bitValue bits) hN .carryTerminal input).accepted] := by
  change [answer bits (List.ofFn input)]=_
  exact congrArg (fun b : Bool=>[b]) (terminal_original bits hc hN input)
/-- Entire original assignment plus original N has linear physical inventory. -/
theorem original_inventory (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (input : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)→Bool) :
    bits.length+(List.ofFn input).length+2≤70*(bitLength (bitValue bits)+1) := by
  rw [List.length_ofFn,←public_width bits hc]
  have h:=cached_length_le bits
  rw [SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc] at h ⊢
  omega
/-- Fixed quadratic actual clock in ORIGINAL bitlength, before every finite
assignment of either original carry endpoint. -/
theorem original_time (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (input : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)→Bool) :
    runBound bits (List.ofFn input)≤100000000000000*(bitLength (bitValue bits)+1)^2 := by
  have h:=Nat.pow_le_pow_left (original_inventory bits hc input) 2
  rw [mul_pow] at h
  norm_num at h
  unfold runBound
  simp only [List.length_ofFn]
  omega
/-- Whole SAME genuine machine certificate on every original finite word. -/
noncomputable def machineOriginal (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (input : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)→Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn input)))
      (some (SemiprimeD1StackCalls.configuration (done bits (List.ofFn input))))
      (100000000000000*(bitLength (bitValue bits)+1)^2) := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0) hN
  let h:=checkInTime bits (List.ofFn input) hb
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (original_time bits hc input)⟩
/-- ALL38 data roles and real return-label cells at EVERY actual machine prefix,
uniformly in original binary width and every carry endpoint assignment. -/
theorem original_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (input : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)→Bool)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn input))))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤10000000000000000*(bitLength (bitValue bits)+1)^2 := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0) hN
  have h:=machine_prefix_cells bits (List.ofFn input) hb fuel cfg hr
  have hp:=Nat.pow_le_pow_left (original_inventory bits hc input) 2
  rw [mul_pow] at hp
  norm_num at hp
  simp only [List.length_ofFn] at h
  omega
end RiemannGaussian.SemiprimeD1StackPublicZeroOriginal
