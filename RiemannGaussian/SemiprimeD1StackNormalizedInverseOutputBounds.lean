/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseStateBounds
import RiemannGaussian.SemiprimeD1StackNormalizedInverseEncoding
/-! # Actual chronological output widths and complete final-cleanup input mass -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseOutputBounds
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseWidths SemiprimeD1StackNormalizedInverseBankBounds
open SemiprimeD1StackNormalizedInverseStateBounds SemiprimeD1StackNormalizedInverseEncoding
open SemiprimeD1StackNormalizedInverseOuterView SemiprimeD1StackNormalizedInverseFinishBuffers
open SemiprimeD1StackNormalizedInverseReadBuffers
/-- Every coefficient field, tag and delimiter contributes its literal byte count. -/
theorem tape_sum (words : List SemiprimeRationalBits.RationalWord) :
    (tape words).length=(words.map (fun word=>2*bytes word+3)).sum+1 := by
  induction words with
  | nil=>rfl
  | cons word words ih=>
    change (row word (tape words)).length=(2*bytes word+3)+(words.map (fun x=>2*bytes x+3)).sum+1
    rw [row_bytes,ih]
    omega
/-- Chronological row reversal changes neither padding bytes nor total allocated array size. -/
theorem tape_reverse_length (words : List SemiprimeRationalBits.RationalWord) :
    (tape words.reverse).length=(tape words).length := by
  rw [tape_sum,List.map_reverse,List.sum_reverse,tape_sum]
/-- The actually emitted chronological array is quadratically bounded even for W=0 or invalid denominators. -/
theorem output_length (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    (tape (outputWords a q width)).length ≤ 14*(inputSize a q width)^2 := by
  rw [←tape_reverse_length]
  exact prefix_le a q width q le_rfl
/-- ALL58 actual words before the final54-role drain retain only bounded original metadata and complete output. -/
theorem beforeCleanup_bank (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    BoundedBank (beforeCleanup a q width) (inputSize a q width) (5*inputSize a q width) (14*(inputSize a q width)^2) := by
  let s:=inputSize a q width
  have hs:=inputSize_caps a q width
  have hs2:s ≤ s^2:=Nat.le_pow (by decide:0<2)
  have ha:(tape a).length ≤ 14*s^2:=by nlinarith only [hs.2.1,hs2]
  have hq:q ≤ 14*s^2:=by nlinarith only [hs.2.2.1,hs2]
  have hout:=output_length a q width
  refine ⟨?_,?_,?_⟩
  · intro k
    change (if k=R.aux .template then width else []).length ≤ s
    split
    · exact hs.2.2.2
    · exact Nat.zero_le _
  · intro r den;exact Nat.zero_le _
  · intro k
    cases k <;> first
      | exact Nat.zero_le _
      | exact ha
      | (change (unary q).length ≤ 14*s^2;simpa only [unary,List.length_replicate] using hq)
      | exact hout
/-- Final real cleanup pays every existing source/output byte and every actual role's EOF. -/
theorem beforeCleanup_mass (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    SemiprimeD1StackNormalizedInverseCleanup.mass (store (beforeCleanup a q width)) ≤ 300*(inputSize a q width)^2 :=
  mass_small _ _ (inputSize_caps a q width).1 (beforeCleanup_bank a q width)
/-- The complete actual final row reversal is paid by the SAME acquired coefficient prefix bytes. -/
theorem finishTime_le (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    SemiprimeD1StackNormalizedInverseFinishLoop.finishTime (outputWords a q width).reverse ≤ 280*(inputSize a q width)^2 := by
  have h:=SemiprimeD1StackNormalizedInverseFinishLoop.finishTime_le (outputWords a q width).reverse
  have hp:=prefix_le a q width q le_rfl
  change (tape (outputWords a q width).reverse).length ≤ 14*(inputSize a q width)^2 at hp
  omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseOutputBounds
