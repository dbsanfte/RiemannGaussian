/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformResources
/-! # Uniform original-bitlength public transform resource family -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformOriginalResources
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformMetadata
open SemiprimeD1StackPublicTransformFinite SemiprimeD1StackPublicTransformPublic
open SemiprimeD1StackPublicTransformMachine SemiprimeD1StackPublicTransformBounds
open SemiprimeBitArithmetic SemiprimeMacroParameters SemiprimeMacroGraph SemiprimeMacroEntryBitCheck
private theorem inventory_arithmetic (ell n w : ℕ) (hn : n ≤ 64*ell+1) (hw : w ≤ 64*ell+2) :
    ell+(n*w+n*w)+1 ≤ 10002*(ell+1)^2 := by
  have h:=Nat.mul_le_mul hn hw
  nlinarith
/-- Original FIRST family size, derived from original physical count and width. -/
theorem first_inventory (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.first (t:=secondAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    bits.length+(List.ofFn assignment).length+1 ≤ 10002*(bitLength (bitValue bits)+1)^2 := by
  rw [←first_raw bits hc hN tr j assignment,List.length_ofFn]
  have hn:=SemiprimeD1StackPublicTransformInventory.size_le bits false
  have hw:=SemiprimeD1StackPublicScaleBounds.cached_length bits
  change (cached bits).length ≤ 64*bits.length+2 at hw
  have h:=inventory_arithmetic bits.length (size bits false) (cached bits).length hn hw
  have hwid:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  simpa only [hwid] using h
/-- Original SECOND family size, without a supplied assignment-size answer. -/
theorem second_inventory (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (secondAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.second (r:=firstAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    bits.length+(List.ofFn assignment).length+1 ≤ 10002*(bitLength (bitValue bits)+1)^2 := by
  rw [←second_raw bits hc hN tr j assignment,List.length_ofFn]
  have hn:=SemiprimeD1StackPublicTransformInventory.size_le bits true
  have hw:=SemiprimeD1StackPublicScaleBounds.cached_length bits
  change (cached bits).length ≤ 64*bits.length+2 at hw
  have h:=inventory_arithmetic bits.length (size bits true) (cached bits).length hn hw
  have hwid:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  simpa only [hwid] using h
private theorem scale_polynomial (s ell : ℕ) (h : s ≤ 10002*(ell+1)^2) :
    10^90*s^18 ≤ 10^180*(ell+1)^36 ∧ 10^94*s^18 ≤ 10^184*(ell+1)^36 := by
  have hp:=Nat.pow_le_pow_left h 18
  rw [mul_pow,←pow_mul] at hp
  norm_num only [Nat.reducePow] at hp ⊢
  constructor <;> omega
/-- Uniform FIRST transition bound, constants fixed before N/tr/j/assignment. -/
theorem first_time (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.first (t:=secondAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    runBound bits (List.ofFn assignment) ≤ 10^180*(bitLength (bitValue bits)+1)^36 :=
  (scale_polynomial _ _ (first_inventory bits hc hN tr j assignment)).1
/-- Uniform SECOND transition bound with the ACTUAL normalizer acquisition. -/
theorem second_time (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (secondAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.second (r:=firstAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    runBound bits (List.ofFn assignment) ≤ 10^180*(bitLength (bitValue bits)+1)^36 :=
  (scale_polynomial _ _ (second_inventory bits hc hN tr j assignment)).1
/-- Literal FIRST public verdict in the actual completed machine's output cell. -/
theorem first_output (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.first (t:=secondAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    (done bits (List.ofFn assignment) false (SemiprimeD1StackPublicScaleFinite.selector tr)).data (.aux .output)=
      [(publicBitEntry (bitValue bits) hN (.first tr j) assignment).accepted] := by
  simp only [SemiprimeD1StackPublicTransformMachine.done]
  rw [SemiprimeD1StackPublicTransformOriginal.final_output,first_original bits hc hN tr j assignment]
/-- Literal SECOND public verdict, including every malformed finite assignment. -/
theorem second_output (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (secondAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.second (r:=firstAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    (done bits (List.ofFn assignment) true (SemiprimeD1StackPublicScaleFinite.selector tr)).data (.aux .output)=
      [(publicBitEntry (bitValue bits) hN (.second tr j) assignment).accepted] := by
  simp only [SemiprimeD1StackPublicTransformMachine.done]
  rw [SemiprimeD1StackPublicTransformOriginal.final_output,second_original bits hc hN tr j assignment]
/-- Genuine original-family fixed-machine certificate, with all actual source
and loop reports replaced only by their OWN proved transition bounds. -/
noncomputable def machineFirst (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.first (t:=secondAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn assignment) false (SemiprimeD1StackPublicScaleFinite.selector tr)))
      (some (SemiprimeD1StackCalls.configuration (done bits (List.ofFn assignment) false (SemiprimeD1StackPublicScaleFinite.selector tr))))
      (10^180*(bitLength (bitValue bits)+1)^36) := by
  have h:=SemiprimeD1StackPublicTransformResources.machineCheck bits (List.ofFn assignment) false (SemiprimeD1StackPublicScaleFinite.selector tr) hc hN
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (first_time bits hc hN tr j assignment)⟩
/-- Every real prefix counts ALL204 Boolean data stacks and return labels. -/
theorem first_prefix (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.first (t:=secondAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn assignment) false (SemiprimeD1StackPublicScaleFinite.selector tr))))=some cfg) :
    (∑q : Stack,(cfg.stk (some q)).length)+(cfg.stk none).length ≤ 10^184*(bitLength (bitValue bits)+1)^36 := by
  exact (SemiprimeD1StackPublicTransformResources.machine_prefix_cells bits (List.ofFn assignment) false (SemiprimeD1StackPublicScaleFinite.selector tr) hc hN fuel cfg hr).trans
    (scale_polynomial _ _ (first_inventory bits hc hN tr j assignment)).2
/-- Genuine original-family fixed-machine certificate, with all actual source
and loop reports replaced only by their OWN proved transition bounds. -/
noncomputable def machineSecond (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (secondAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.second (r:=firstAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn assignment) true (SemiprimeD1StackPublicScaleFinite.selector tr)))
      (some (SemiprimeD1StackCalls.configuration (done bits (List.ofFn assignment) true (SemiprimeD1StackPublicScaleFinite.selector tr))))
      (10^180*(bitLength (bitValue bits)+1)^36) := by
  have h:=SemiprimeD1StackPublicTransformResources.machineCheck bits (List.ofFn assignment) true (SemiprimeD1StackPublicScaleFinite.selector tr) hc hN
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (second_time bits hc hN tr j assignment)⟩
/-- Every real prefix counts ALL204 Boolean data stacks and return labels. -/
theorem second_prefix (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (secondAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.second (r:=firstAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn assignment) true (SemiprimeD1StackPublicScaleFinite.selector tr))))=some cfg) :
    (∑q : Stack,(cfg.stk (some q)).length)+(cfg.stk none).length ≤ 10^184*(bitLength (bitValue bits)+1)^36 := by
  exact (SemiprimeD1StackPublicTransformResources.machine_prefix_cells bits (List.ofFn assignment) true (SemiprimeD1StackPublicScaleFinite.selector tr) hc hN fuel cfg hr).trans
    (scale_polynomial _ _ (second_inventory bits hc hN tr j assignment)).2
end RiemannGaussian.SemiprimeD1StackPublicTransformOriginalResources
