/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableBounds
import RiemannGaussian.SemiprimeD1ProductTableOriginal
import Mathlib.Data.Nat.Sqrt
/-! # Whole original product-table acquisition in polynomial times2^O(sqrt ell)
This is the actual fixed N-only machine's OWN bit-time certificate. The full
old table is proved equal at its literal bytes, with each original coefficient
lifted individually. It is a compiler component, not the full factor machine.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableOriginal
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableSpec SemiprimeD1StackProductTableExecution
open SemiprimeMacroParameters SemiprimeBitArithmetic
/-- The actual acquired arity has a quantitative ORIGINAL-bitwidth square-root
bound, derived from the actual dyadic transform stopping rule, not a report. -/
theorem arity_sqrt_le (bits : List Bool) (hb : bits≠[]) : arity bits≤48*(Nat.sqrt bits.length+1) := by
  let R:=transformLength bits.length
  have hL:0<bits.length := by
    cases bits with
    | nil=>exact (hb rfl).elim
    | cons b rest=>exact Nat.zero_lt_succ _
  have hR:0<R := by dsimp [R,transformLength];positivity
  have hR2:R^2<64*bits.length:=transform_square_upper hL
  have ha:arity bits≤6*R := by
    unfold arity
    rw [SemiprimeD1StackPublicProductBounds.cached_length]
    change 3*(R+1)≤6*R
    omega
  have hr:R≤8*(Nat.sqrt bits.length+1) := by
    by_contra hn
    have he:8*(Nat.sqrt bits.length+1)<R := by omega
    have hp:=Nat.pow_lt_pow_left he (by decide : (2:ℕ)≠0)
    rw [mul_pow] at hp
    change 64*(Nat.sqrt bits.length+1)^2<R^2 at hp
    have hs:bits.length<(Nat.sqrt bits.length+1)^2:=by
      simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' bits.length
    omega
  calc
    _ ≤ 6*R :=ha
    _ ≤ 6*(8*(Nat.sqrt bits.length+1)) :=Nat.mul_le_mul_left _ hr
    _ = _ :=by ring
/-- Explicit whole source bit-time envelope using the original input WIDTH. -/
def sqrtBound (bits : List Bool) : ℕ :=1000000000000000000000000000000*(bits.length+1)^3*2^(48*(Nat.sqrt bits.length+1))
/-- Actual full original-N runtime bound is polynomial times2^O(sqrt width). -/
theorem runBound_le_sqrt (bits : List Bool) (hb : bits≠[]) :
    SemiprimeD1StackProductTableBounds.runBound bits≤ sqrtBound bits :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (arity_sqrt_le bits hb))
/-- Exact OLD original product table tape, for every product position and ALL
original assignments in their old local-port order, on the actual output role. -/
theorem output_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits)))) :
    (done bits).data (.inr .output)=SemiprimeD1TensorTapeCodec.tape
      (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl (.product k))) :=
  (output_table bits).trans (SemiprimeD1ProductTableOriginal.output_original bits hc hN k)
/-- A genuine N-only machine certificate with the quantitative square-root
exponent and ALL acquisition/arithmetic/output/address/cleanup calls retained. -/
noncomputable def machineOriginal (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (1000000000000000000000000000000*(bitLength (bitValue bits)+1)^3*
        2^(48*(Nat.sqrt (bitLength (bitValue bits))+1))) := by
  have hb:bits≠[] :=by intro h;rw [h] at hN;exact Nat.lt_irrefl 0 hN
  have h:=SemiprimeD1StackProductTableBounds.machineTable bits hb
  have ht:=runBound_le_sqrt bits hb
  unfold sqrtBound at ht
  rw [SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc] at ht
  exact ⟨h.toEvalsTo,h.steps_le_m.trans ht⟩
/-- Every original-input prefix of the SAME finite machine has a complete
all83-role/real-return inventory at the quantitative square-root envelope. -/
theorem original_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      84*(bitLength (bitValue bits)+1000000000000000000000000000000*(bitLength (bitValue bits)+1)^3*
        2^(48*(Nat.sqrt (bitLength (bitValue bits))+1))) := by
  have hb:bits≠[] :=by intro h;rw [h] at hN;exact Nat.lt_irrefl 0 hN
  have hs:=SemiprimeD1StackProductTableBounds.machine_prefix_cells bits hb fuel cfg hr
  have ht:=runBound_le_sqrt bits hb
  have he:bits.length=bitLength (bitValue bits):=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  unfold sqrtBound at ht
  rw [he] at hs ht
  omega
end RiemannGaussian.SemiprimeD1StackProductTableOriginal
