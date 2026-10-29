/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputs
/-! # Exact shared rational-array bytes across actual affine, inverse and powers calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsCodec
open SemiprimeSourceHistogramKeyBits (frame)
/-- Existing framed payloads append their actual tail without changing any signed or high-zero byte. -/
theorem frame_append (word xs ys : List Bool) : frame word xs++ys=frame word (xs++ys) := by
  induction word with
  | nil=>rfl
  | cons b word ih=>
    change true::b::(frame word xs++ys)=true::b::frame word (xs++ys)
    rw [ih]
/-- The actual old affine output ABI is EXACTLY the complete inverse input ABI, not a decoded/value-only conversion. -/
theorem affine_tape (words : List SemiprimeRationalBits.RationalWord) :
    SemiprimeD1StackRecoveryAffineView.vector words=SemiprimeD1StackNormalizedInverse.tape words := rfl
/-- A real chronological powers row has exactly the same two signed/denominator frames and TRUE tag. -/
theorem powers_row (word : SemiprimeRationalBits.RationalWord) (tail : List Bool) :
    SemiprimeD1StackRecoveryPowersSpec.row word++tail=SemiprimeD1StackNormalizedInverse.row word tail := by
  unfold SemiprimeD1StackRecoveryPowersSpec.row SemiprimeD1StackNormalizedInverse.row
  rw [List.cons_append,frame_append,frame_append,List.nil_append]
  rfl
/-- The complete ACTUAL powers source output is directly readable by the already literal inverse array readers. -/
theorem powers_tape (words : List SemiprimeRationalBits.RationalWord) :
    SemiprimeD1StackRecoveryPowersSpec.vector words=SemiprimeD1StackNormalizedInverse.tape words := by
  induction words with
  | nil=>rfl
  | cons word words ih=>
    change SemiprimeD1StackRecoveryPowersSpec.row word++SemiprimeD1StackRecoveryPowersSpec.vector words=
      SemiprimeD1StackNormalizedInverse.row word (SemiprimeD1StackNormalizedInverse.tape words)
    rw [ih,powers_row]
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsCodec
