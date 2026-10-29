/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeView
/-! # Actual whole Node140 cache supplies all operands of complete local weight acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeEncoding
open SemiprimeD1StackRecoveryNode
namespace Old
export SemiprimeD1StackRecoveryWeightsLegacy (grid inverse powers retained)
end Old
namespace V
export SemiprimeD1StackRecoveryNodeView (empty result)
end V
/-- Exact original q from actual acquired geometry/metadata, only a proof-side specification. -/
def q (a M u:ℕ) (selected:Fin (2^(a+1))):ℕ:=Old.retained a M u selected
/-- Actual Grid-derived scalar specification; no scalar operand in original five-word input. -/
def scalar (a M u:ℕ) (selected:Fin (2^(a+1))) (width:List Bool):SemiprimeRationalBits.RationalWord:=(Old.grid width a M u selected).scalar
/-- Exact raw native complete local coefficient list produced by actual weight calls. -/
def words (a M u:ℕ) (selected:Fin (2^(a+1))) (width:List Bool):List SemiprimeRationalBits.RationalWord:=
  SemiprimeD1StackRecoveryWeightsSpec.array width (q a M u selected) (scalar a M u selected width)
    (Old.inverse width a M u selected) (Old.powers width a M u selected)
/-- Exact chronological acquired rational-array tape. -/
def tape (a M u:ℕ) (selected:Fin (2^(a+1))) (width:List Bool):List Bool:=SemiprimeD1StackNormalizedInverse.tape (words a M u selected width)
/-- Complete original Node140 source has actually stopped; all141st-word bytes remain EMPTY. -/
def afterNode (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool):Stack→List Bool:=
  V.empty (SemiprimeD1StackRecoveryNodeInputsEncoding.result a M u selected t width)
/-- Only one newly acquired output is added; all140 actual stopped cache words are retained. -/
def result (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool):Stack→List Bool:=
  V.result (SemiprimeD1StackRecoveryNodeInputsEncoding.result a M u selected t width) (tape a M u selected width)
/-- Actual whole halt has no transient flags or internal saved returns. -/
def done (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool):C.State Stack Label:=⟨none,none,none,result a M u selected t width,[]⟩
/-- SAME actual already-acquired Grid104 cache entry; no q/affine/inverse/power/weight answers. -/
def gridReady (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool):C.State Stack Label:=
  ⟨some (ctl .readyGrid),none,none,V.empty (SemiprimeD1StackRecoveryNodeInputsEncoding.gridReady a M u selected t width).data,[]⟩
/-- Native inverse byte lineage is exact, not merely an inverse value equality. -/
theorem inverse_original (a M u:ℕ) (selected:Fin (2^(a+1))) (width:List Bool):
    SemiprimeD1StackRecoveryNodeInputsEncoding.inverseWords a M u selected width=Old.inverse width a M u selected:=
  SemiprimeD1StackRecoveryNodeInputsOriginal.inverse_native a M u selected width
/-- Native power bytes use precisely the same actual recurrence/operand order. -/
theorem powers_original (a M u:ℕ) (selected:Fin (2^(a+1))) (width:List Bool):
    SemiprimeD1StackRecoveryNodeInputsEncoding.powerWords a M u selected width=Old.powers width a M u selected:=rfl
/-- Every real acquired operand and clean helper word is already in the physically shared bank. -/
theorem weight_initial (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool):
    SemiprimeD1StackMultiplierLink.DataRel weight (afterNode a M u selected t width)
      (W.initial (SemiprimeD1StackNormalizedInverse.tape (Old.inverse width a M u selected))
        (SemiprimeD1StackNormalizedInverse.tape (Old.powers width a M u selected))
        (SemiprimeD1StackNormalizedInverse.signed (scalar a M u selected width))
        (scalar a M u selected width).denominator (List.replicate (q a M u selected) true) width).data
      (afterNode a M u selected t width):=by
  have h:=SemiprimeD1StackRecoveryNodeView.weight_initial
    (SemiprimeD1StackRecoveryAffineEncoding.result a M u selected t width)
    (SemiprimeD1StackRecoveryNodeInputsEncoding.inverseTape a M u selected width)
    (SemiprimeD1StackRecoveryNodeInputsEncoding.powerTape a M u selected width)
    (SemiprimeD1StackNormalizedInverse.signed (scalar a M u selected width))
    (scalar a M u selected width).denominator (List.replicate (q a M u selected) true) width
    (SemiprimeD1StackRecoveryNodeInputsEncoding.rational_image a M u selected t width) rfl rfl rfl
  unfold SemiprimeD1StackRecoveryNodeInputsEncoding.inverseTape at h
  rw [inverse_original,SemiprimeD1StackRecoveryNodeInputsEncoding.power_tape,powers_original] at h
  simpa only [afterNode,SemiprimeD1StackRecoveryNodeInputsEncoding.result,
    SemiprimeD1StackRecoveryNodeInputsEncoding.inverseTape,SemiprimeD1StackRecoveryNodeInputsEncoding.power_tape,
    inverse_original,powers_original,W.initial] using h
end RiemannGaussian.SemiprimeD1StackRecoveryNodeEncoding
