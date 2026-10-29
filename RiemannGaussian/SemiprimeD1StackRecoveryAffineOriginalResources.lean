/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineStorage
import RiemannGaussian.SemiprimeD1StackRecoveryAffineValues
/-! # Original-dimension and acquired-root metadata resource caps for the SAME affine source
This pays original width and grid size by VALUE through the physical source.
It does not assert the later N-only caller join or completed recursive counter.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineOriginalResources
open SemiprimeD1StackRecoveryAffine
namespace D
export SemiprimeD1StackRecoveryGridOriginalResources (dimensions resource_le root_dimensions)
end D
namespace W
export SemiprimeD1StackRecoveryWidthOriginal (originalA originalM sizingCoefficient)
end W
/-- Actual original-dimension template VALUE suffices for this SAME fixed source's complete original-grid affine acquisition. -/
theorem original_clock (a M u:Nat) (selected:Fin (2^(a+1))) (t:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u≤ M):
    SemiprimeD1StackRecoveryAffineExecution.timeBound a M u selected t
      (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false)≤ 10^150*(D.dimensions a M t)^70:=by
  have h:=SemiprimeD1StackRecoveryAffineBounds.timeBound_le a M u selected t
    (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false) ht
  have hp:=Nat.pow_le_pow_left (D.resource_le a M u t hu) 14
  have hm:=Nat.mul_le_mul_left (10^75) hp
  unfold SemiprimeD1StackRecoveryAffineBounds.polynomial at h
  rw [mul_pow,←pow_mul] at hm
  norm_num1 at hm ⊢
  omega
/-- Every actual112-word and real-return prefix has a fixed original-dimension polynomial cap. -/
theorem original_space (a M u:Nat) (selected:Fin (2^(a+1))) (t:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u≤ M) (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t
        (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false))))=some cfg):
    (∑slot:Stack,(cfg.stk (some slot)).length)+(cfg.stk none).length≤ 10^153*(D.dimensions a M t)^70:=by
  have h:=SemiprimeD1StackRecoveryAffineStorage.machine_prefix_cells a M u selected t _ ht fuel cfg hp
  have hm:=Nat.mul_le_mul_left (10^78) (Nat.pow_le_pow_left (D.resource_le a M u t hu) 14)
  unfold SemiprimeD1StackRecoveryAffineStorage.spacePolynomial at h
  rw [mul_pow,←pow_mul] at hm
  norm_num1 at hm ⊢
  omega
/-- Fixed coefficient precedes every original binary N and every actually reached node. -/
def globalCoefficient:Nat:=10^150*(4*W.sizingCoefficient)^70
/-- Actual acquired original a/M and bounded binary-index padding give a fixed polynomial-in-ell source cost. -/
theorem root_clock (bits t:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) (u:Nat) (hu:u≤ W.originalM bits)
    (selected:Fin (2^(W.originalA bits+1))) (ht:SemiprimeBitArithmetic.bitValue t=selected.val)
    (hbytes:t.length≤ W.originalA bits+2):
    SemiprimeD1StackRecoveryAffineExecution.timeBound (W.originalA bits) (W.originalM bits) u selected t
      (List.replicate (SemiprimeD1RecoveryNodeBits.width (W.originalA bits) (W.originalM bits)) false)≤
      globalCoefficient*(bits.length+1)^700:=by
  have h:=original_clock (W.originalA bits) (W.originalM bits) u selected t ht hu
  have hm:=Nat.mul_le_mul_left (10^150) (Nat.pow_le_pow_left (D.root_dimensions bits t hc hN hbytes) 70)
  rw [mul_pow,←pow_mul] at hm
  unfold globalCoefficient
  simpa only [Nat.mul_assoc,show 10*70=700 by decide] using h.trans hm
end RiemannGaussian.SemiprimeD1StackRecoveryAffineOriginalResources
