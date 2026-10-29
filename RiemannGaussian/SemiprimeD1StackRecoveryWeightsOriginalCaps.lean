/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsOriginal
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsWidths
import RiemannGaussian.SemiprimeD1StackRecoveryAffineResource
/-! # Actual original inverse/powers/scalar bytes derive from fitted fields and acquired q/W VALUES -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsOriginalCaps
open SemiprimeD1StackRecoveryWeightsLegacy SemiprimeD1StackRecoveryWeightsWidths
open SemiprimeRationalBits (RationalWord)
namespace P
export SemiprimeD1StackRecoveryPowersSpec (suffix next array from_length)
end P
namespace R
export SemiprimeD1StackRecoveryGridResource (resource resource_pos width_le)
end R
/-- Each actually cached successor is fitted; only the literal ONE has the one-byte exception at W0. -/
theorem suffix_bytes (width:List Bool) (argument current:RationalWord) (q:Nat)
    (hc:B.bytes current ≤ 2*width.length+3):∀word∈P.suffix width argument current q,B.bytes word ≤ 2*width.length+3:=by
  induction q generalizing current with
  | zero=>intro word hw;exact (List.not_mem_nil hw).elim
  | succ q ih=>
    intro word hw
    rcases List.mem_cons.mp hw with h|h
    · subst word;exact hc
    · apply ih _ (by have hh:B.bytes (P.next width argument current)=2*width.length+1:=B.execute_bytes .mul current argument width;omega) word h
/-- Complete original inverse tape is bounded by the actual q/W values, independently of denominator magnitudes. -/
theorem inverse_bytes (width:List Bool) (a M u:Nat) (selected:Fin (2^(a+1))):
    (SemiprimeD1StackNormalizedInverse.tape (inverse width a M u selected)).length ≤ retained a M u selected*(4*width.length+9)+1:=by
  have h:=B.tape_bytes (inverse width a M u selected) (2*width.length+3)
    (SemiprimeD1StackNormalizedInverseWidths.build_bytes width _ (retained a M u selected))
  simpa only [inverse,Array.length_toList,SemiprimeNormalizedInverseBits.build_size,
    show 2*(2*width.length+3)+3=4*width.length+9 by omega] using h
/-- Exact chronological cached powers keep the literal ONE and all original padding, with the same paid field cap. -/
theorem powers_bytes (width:List Bool) (a M u:Nat) (selected:Fin (2^(a+1))):
    (SemiprimeD1StackNormalizedInverse.tape (powers width a M u selected)).length ≤ retained a M u selected*(4*width.length+9)+1:=by
  have h:=B.tape_bytes (powers width a M u selected) (2*width.length+3)
    (suffix_bytes width (grid width a M u selected).argument SemiprimeJetBits.oneWord (retained a M u selected)
      (by rw [SemiprimeD1StackNormalizedInverseWidths.one_bytes];omega))
  simpa only [powers,P.array,P.from_length,show 2*(2*width.length+3)+3=4*width.length+9 by omega] using h
/-- Ezero itself is the actual final normalized/twice-fitted Grid multiplication, with no canonical-value width shortcut. -/
theorem scalar_bytes (width:List Bool) (a M u:Nat) (selected:Fin (2^(a+1))):
    B.bytes (grid width a M u selected).scalar=2*width.length+1:=B.execute_bytes .mul _ _ width
/-- Every six-word input byte is paid by acquired q/W and true Grid enumeration, before any weight operation starts. -/
theorem inputSize_le (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    inputSize (inverse width a M u selected) (powers width a M u selected) (grid width a M u selected).scalar
      (retained a M u selected) width ≤ 1000*(R.resource a M u t width)^2:=by
  let r:=R.resource a M u t width
  have hr:1 ≤ r:=R.resource_pos a M u t width
  have hw:width.length ≤ r:=R.width_le a M u t width
  have hq:retained a M u selected ≤ 3*r:=SemiprimeD1StackRecoveryAffineResource.q_le a M u selected t width
  have hi:=inverse_bytes width a M u selected
  have hp:=powers_bytes width a M u selected
  have hz:=scalar_bytes width a M u selected
  have hqw:retained a M u selected*width.length ≤ 3*r^2:=by
    have h:=Nat.mul_le_mul hq hw
    simpa only [pow_two,Nat.mul_assoc] using h
  have hr2:r ≤ r^2:=Nat.le_pow (by decide:0<2)
  have h12:1 ≤ r^2:=Nat.one_le_pow _ _ hr
  unfold inputSize
  nlinarith only [hi,hp,hz,hq,hw,hqw,hr2,h12]
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsOriginalCaps
