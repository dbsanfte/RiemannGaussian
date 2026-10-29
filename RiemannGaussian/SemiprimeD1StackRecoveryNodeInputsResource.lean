/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsExecution
/-! # Actual acquired inverse/power operand byte caps
These semantic byte bounds charge the physically enumerated grid and W VALUES.
They do not obtain arithmetic operand widths from elapsed execution.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsResource
open SemiprimeD1StackRecoveryNodeInputs SemiprimeD1StackRecoveryNodeInputsEncoding
namespace R
export SemiprimeD1StackRecoveryGridResource (resource resource_pos cacheWidth cache_le width_le)
end R
namespace B
export SemiprimeD1StackRecoveryAffineByteCaps (Small one_small multiply_small vector_length)
end B
/-- Every raw native affine suffix is fitted or the literal ONE, even W0. -/
theorem build_small (width : List Bool) (q : ℕ) (slopes : List SemiprimeRationalBits.RationalWord) :
    ∀x∈(SemiprimeAffineJetBits.build width q slopes).words.toList,B.Small width x := by
  cases slopes with
  | nil=>
    intro x hx
    change x∈[SemiprimeJetBits.oneWord] at hx
    rw [List.mem_singleton] at hx
    subst x
    exact B.one_small width
  | cons c cs=>
    have h:=B.multiply_small width (SemiprimeAffineJetBits.build width q cs).words.toList c q
    simpa only [SemiprimeD1StackRecoveryAffineLoopView.multiply,Array.toArray_toList,SemiprimeAffineJetBits.build,SemiprimeAffineJetBits.affine] using h
/-- Actual denominator-array framed bytes have a cubic physical cap, including the empty-product literal. -/
theorem denominator_bytes (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    (SemiprimeD1StackNormalizedInverse.tape (E.array a M u selected width)).length≤10^9*(R.resource a M u t width)^3 := by
  have hs:=build_small width (E.retained a M u selected) (SemiprimeD1RecoveryGridBits.acquire width a M u selected).grid.slopes
  have hb:=B.vector_length width (E.array a M u selected width) hs
  have hn:(E.array a M u selected width).length≤E.retained a M u selected+1:=by
    unfold E.array
    rw [Array.length_toList,SemiprimeAffineJetBits.build_size]
    split <;> omega
  have hbudget:=SemiprimeD1StackRecoveryAffineResource.array_budget a M u selected t width
  change _≤10^9*(R.resource a M u t width)^3 at hbudget
  rw [←SemiprimeD1StackRecoveryNodeInputsCodec.affine_tape]
  exact hb.trans ((Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1).trans hbudget)
/-- The real inverse input size is bounded from actual fitted words and acquired unary metadata. -/
theorem inverse_size (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    SemiprimeD1StackNormalizedInverseStateBounds.inputSize (E.array a M u selected width) (E.retained a M u selected) width≤
      10^10*(R.resource a M u t width)^3 := by
  have hb:=denominator_bytes a M u selected t width
  have hq:=SemiprimeD1StackRecoveryAffineResource.q_le a M u selected t width
  have hw:=R.width_le a M u t width
  have hr:=R.resource_pos a M u t width
  have hp:R.resource a M u t width≤(R.resource a M u t width)^3:=Nat.le_pow (by decide:0<3)
  unfold SemiprimeD1StackNormalizedInverseStateBounds.inputSize
  omega
/-- Actual retained argument fields use semantic Grid register caps, never report clocks. -/
theorem argument_bytes (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    (SemiprimeD1StackRecoveryPowersSpec.signed (argument a M u selected width)).length≤R.cacheWidth a width ∧
      (argument a M u selected width).denominator.length≤R.cacheWidth a width := by
  have h:=(SemiprimeD1StackRecoveryAffineInitialCaps.original_caps a M u selected t width ht).1
  exact ⟨h .argument false,h .argument true⟩
/-- The whole powers call reads only those actual Grid fields, acquired q and preserved W. -/
theorem powers_size (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    SemiprimeD1StackRecoveryPowersEncoding.resource (argument a M u selected width) (E.retained a M u selected) width≤
      10*(R.resource a M u t width) := by
  obtain ⟨ha,hd⟩:=argument_bytes a M u selected t width ht
  have hc:=R.cache_le a M u t width
  have hq:=SemiprimeD1StackRecoveryAffineResource.q_le a M u selected t width
  have hw:=R.width_le a M u t width
  have hr:=R.resource_pos a M u t width
  unfold SemiprimeD1StackRecoveryPowersEncoding.resource
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsResource
