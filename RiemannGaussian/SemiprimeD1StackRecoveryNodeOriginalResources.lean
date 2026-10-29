/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeOriginal
/-! # Original dimension/root metadata caps for this SAME whole Node-weight source
W and the true grid enumeration are charged by their actual materialized VALUES.
The N-only outercaller and recursive scalar counter remain separate joins.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeOriginalResources
open SemiprimeD1StackRecoveryNode SemiprimeD1StackRecoveryNodeBounds
namespace D
export SemiprimeD1StackRecoveryGridOriginalResources (dimensions resource_le root_dimensions)
end D
namespace W
export SemiprimeD1StackRecoveryWidthOriginal (originalA originalM sizingCoefficient)
end W
/-- Abstract dimension scaling is proved before substituting actual original banks/metadata. -/
theorem dimension_scale (r d : ℕ) (h : r≤10000*d^5) :10^151*r^30≤10^271*d^150 := by
  have hm:=Nat.mul_le_mul_left (10^151) (Nat.pow_le_pow_left h 30)
  rw [mul_pow] at hm
  convert hm using 1
  ring
/-- Every originally paid physical width and actual grid VALUE fits a fixed whole-source dimension polynomial. -/
theorem original_clock (a M u : ℕ) (selected : Fin (2^(a+1))) (t : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) (hu : u≤M) :
    SemiprimeD1StackRecoveryNodeExecution.runBound a M u selected t
      (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false)≤10^271*(D.dimensions a M t)^150 :=
  (runBound_le a M u selected t _ ht).trans (dimension_scale _ _ (D.resource_le a M u t hu))
/-- Complete prepared actual source, not an N-only scalar counter, has this original-family clock. -/
theorem source_run_original_bounded (a M u : ℕ) (selected : Fin (2^(a+1))) (t : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) (hu : u≤M) :
    ∃s≤10^271*(D.dimensions a M t)^150,SemiprimeD1StackCalls.run program s
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t
        (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false))=
      some (SemiprimeD1StackRecoveryNodeEncoding.done a M u selected t
        (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false)) := by
  obtain ⟨s,hs,hr⟩:=SemiprimeD1StackRecoveryNodeExecution.source_run a M u selected t _ ht
  exact ⟨s,hs.trans (original_clock a M u selected t ht hu),hr⟩
/-- All physical words and saved return cells have the same original-dimension polynomial degree. -/
theorem original_space (a M u : ℕ) (selected : Fin (2^(a+1))) (t : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) (hu : u≤M) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t
        (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false))))=some cfg) :
    (∑role : Stack,(cfg.stk (some role)).length)+(cfg.stk none).length≤10^274*(D.dimensions a M t)^150 := by
  have hb:=SemiprimeD1StackRecoveryNodeStorage.machine_prefix_cells a M u selected t _ ht fuel cfg hp
  have hd:=dimension_scale _ _ (D.resource_le a M u t hu)
  have hs:SemiprimeD1StackRecoveryNodeStorage.cellsPolynomial a M u t
      (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false)≤10^274*(D.dimensions a M t)^150:=by
    unfold SemiprimeD1StackRecoveryNodeStorage.cellsPolynomial
    calc
      _=1000*(10^151*(SemiprimeD1StackRecoveryGridResource.resource a M u t
        (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false))^30):=by ring
      _≤1000*(10^271*(D.dimensions a M t)^150):=Nat.mul_le_mul_left 1000 hd
      _=_:=by ring
  exact hb.trans hs
/-- Fixed coefficient precedes every original binary N and every selected phase. -/
def globalCoefficient : ℕ :=10^271*(4*W.sizingCoefficient)^150
/-- Actual acquired original root metadata and bounded binary padding specialize the SAME source clock. -/
theorem root_clock (bits t : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (u : ℕ) (hu : u≤W.originalM bits)
    (selected : Fin (2^(W.originalA bits+1))) (ht : SemiprimeBitArithmetic.bitValue t=selected.val)
    (hbytes : t.length≤W.originalA bits+2) :
    SemiprimeD1StackRecoveryNodeExecution.runBound (W.originalA bits) (W.originalM bits) u selected t
      (List.replicate (SemiprimeD1RecoveryNodeBits.width (W.originalA bits) (W.originalM bits)) false)≤
      globalCoefficient*(bits.length+1)^1500 := by
  have h:=original_clock (W.originalA bits) (W.originalM bits) u selected t ht hu
  have hm:=Nat.mul_le_mul_left (10^271) (Nat.pow_le_pow_left (D.root_dimensions bits t hc hN hbytes) 150)
  rw [mul_pow,←pow_mul] at hm
  unfold globalCoefficient
  simpa only [Nat.mul_assoc,show 10*150=1500 by decide] using h.trans hm
end RiemannGaussian.SemiprimeD1StackRecoveryNodeOriginalResources
