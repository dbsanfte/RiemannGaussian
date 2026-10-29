/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridStorage
import RiemannGaussian.SemiprimeD1StackRecoveryGridValues
import RiemannGaussian.SemiprimeD1StackRecoveryWidthOriginal
/-! # Original-family paid-width/value bounds without coefficient or report-clock advice
The source remains the honest five-word stage. Root dimension bounds specialize
its resource only; a literal N-only caller composition is a separate obligation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridOriginalResources
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridBounds
namespace R
export SemiprimeD1StackRecoveryGridResource (resource gridSize)
end R
namespace V
export SemiprimeD1StackRecoveryWidthPolynomial (value value_bound envelope last_original)
end V
namespace W
export SemiprimeD1StackRecoveryWidthOriginal (originalA originalM original_envelope sizingCoefficient)
end W
/-- Original dimensions include true enumeration VALUE and every actual binary selected-index byte. -/
def dimensions (a M:Nat) (t:List Bool) :Nat:=a+M+t.length+R.gridSize a+1
/-- Every output W cell is paid by the original literal width polynomial, before coefficient arithmetic starts. -/
theorem width_le (a M:Nat) (t:List Bool) :SemiprimeD1RecoveryNodeBits.width a M≤2000*(dimensions a M t)^5:=by
  have h:=V.value_bound 63 a M (R.gridSize a)
  dsimp only [R.gridSize] at h
  rw [V.last_original a M] at h
  have hm:V.envelope a M (R.gridSize a)≤dimensions a M t:=by unfold V.envelope dimensions;omega
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 5))
/-- Every original u/t/W/source/output byte fits a fixed dimension polynomial; W is paid by VALUE. -/
theorem resource_le (a M u:Nat) (t:List Bool) (hu:u≤M) :
    R.resource a M u t (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false)≤10000*(dimensions a M t)^5:=by
  have hw:=width_le a M t
  have hD:1≤dimensions a M t:=by unfold dimensions;omega
  have hp:dimensions a M t≤(dimensions a M t)^5:=Nat.le_pow (by decide:0<5)
  unfold R.resource
  rw [List.length_replicate]
  unfold dimensions at hw hp ⊢
  omega
/-- The same whole original-grid source has a uniform dimension cap, with every width/enumeration VALUE cost included. -/
theorem original_clock (a M u:Nat) (t:List Bool) (hu:u≤M) :
    SemiprimeD1StackRecoveryGridExecution.runBound a M u t (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false)≤
      10^110*(dimensions a M t)^60:=by
  have h:=runBound_le a M u t (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false)
  have hp:=Nat.pow_le_pow_left (resource_le a M u t hu) 12
  have hm:=Nat.mul_le_mul_left (10^60) hp
  unfold polynomial at h
  rw [mul_pow,←pow_mul] at hm
  norm_num1 at hm ⊢
  omega
/-- All104 data tapes and actual saved returns have the corresponding uniform dimension bound. -/
theorem original_space (a M u:Nat) (t:List Bool) (hu:u≤M) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t
        (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤10^113*(dimensions a M t)^60:=by
  have h:=SemiprimeD1StackRecoveryGridStorage.machine_prefix_cells a M u t _ fuel cfg hr
  have hp:=Nat.pow_le_pow_left (resource_le a M u t hu) 12
  have hm:=Nat.mul_le_mul_left (10^63) hp
  rw [mul_pow,←pow_mul] at hm
  norm_num1 at hm ⊢
  omega
/-- Actual retained root a/M metadata bounds the original dimensions; binary index padding is charged explicitly. -/
theorem root_dimensions (bits t:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) (ht:t.length≤W.originalA bits+2) :
    dimensions (W.originalA bits) (W.originalM bits) t≤
      4*W.sizingCoefficient*(bits.length+1)^10:=by
  have h:=W.original_envelope bits hc hN
  change W.originalA bits+W.originalM bits+R.gridSize (W.originalA bits)+1≤_ at h
  have hs:1≤W.sizingCoefficient*(bits.length+1)^10:=by
    unfold W.sizingCoefficient
    have hp:1≤(bits.length+1)^10:=Nat.one_le_pow 10 _ (by omega)
    norm_num1
    omega
  calc
    _≤4*(W.sizingCoefficient*(bits.length+1)^10):=by unfold dimensions;omega
    _=_:=by ring
/-- A fixed coefficient before all N pays this stage at the acquired original root dimensions. -/
def globalCoefficient :Nat:=10^110*(4*W.sizingCoefficient)^60
/-- Original-root specialization uses semantic schedule/edge bounds and the SAME new source clock, never an old report clock. -/
theorem root_clock (bits t:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) (u:Nat) (hu:u≤W.originalM bits)
    (ht:t.length≤W.originalA bits+2) :
    SemiprimeD1StackRecoveryGridExecution.runBound (W.originalA bits) (W.originalM bits) u t
      (List.replicate (SemiprimeD1RecoveryNodeBits.width (W.originalA bits) (W.originalM bits)) false)≤
      globalCoefficient*(bits.length+1)^600:=by
  have h:=original_clock (W.originalA bits) (W.originalM bits) u t hu
  have hm:=Nat.mul_le_mul_left (10^110) (Nat.pow_le_pow_left (root_dimensions bits t hc hN ht) 60)
  rw [mul_pow,←pow_mul] at hm
  unfold globalCoefficient
  simpa only [Nat.mul_assoc,show 10*60=600 by decide] using h.trans hm
end RiemannGaussian.SemiprimeD1StackRecoveryGridOriginalResources
