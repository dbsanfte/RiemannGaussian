/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishWords
/-! # Exact compact final words despite arbitrary quotient padding
Integer floor correctness is proved separately. Compact target-width residue
uniqueness is used only after real modular reduction, never to identify padded
raw quotient words or silently change the Newton-product/sum order.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishResidue
open SemiprimeBitArithmetic
open SemiprimeBitIndexClipping (SignedWord)
open SemiprimeD1StackRecoveryFinishWords
namespace J
export SemiprimeD1JetScalarBits (reduce mul reduce_length reduce_compact mul_length mul_compact mul_zmod)
end J
/-- Two compact actual target-width words with the same target-ring value have identical Boolean bytes. -/
theorem canonical_eq (p:Nat) (a b:List Bool) (ha:SemiprimeSourceCompactBits.Compact a)
    (hb:SemiprimeSourceCompactBits.Compact b) (hla:a.length≤p) (hlb:b.length≤p)
    (h:(bitValue a:ZMod (2^p))=(bitValue b:ZMod (2^p))):a=b:=by
  have hva:bitValue a<2^p:=(bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by decide:1≤2) hla)
  have hvb:bitValue b<2^p:=(bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by decide:1≤2) hlb)
  have hv:=congrArg ZMod.val h
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hva,Nat.mod_eq_of_lt hvb] at hv
  exact SemiprimeSourceCompactWordIds.compact_value_injective _ _ ha hb hv
/-- Reducing a binary operand before the real canonical modular product preserves exact output bytes. -/
theorem mul_reduce_right (p:Nat) (a b:List Bool):
    (J.mul p a (J.reduce p b).bits).bits=(J.mul p a b).bits:=by
  apply canonical_eq p _ _ (J.mul_compact _ _ _) (J.mul_compact _ _ _)
    (J.mul_length _ _ _) (J.mul_length _ _ _)
  simp only [J.mul_zmod,SemiprimeD1JetScalarBits.reduce_value,ZMod.natCast_mod]
/-- Canonical signed residue depends on the actual signed floor VALUE, not on arbitrary quotient padding. -/
theorem signed_congr (p:Nat) (a b:SignedWord) (h:a.value=b.value):
    (Old.signed p a).bits=(Old.signed p b).bits:=by
  have ha:=SemiprimeD1RecoveryStripBits.signed_good p a
  have hb:=SemiprimeD1RecoveryStripBits.signed_good p b
  apply canonical_eq p _ _ ha.2 hb.2 ha.1 hb.1
  rw [SemiprimeD1RecoveryStripBits.signed_value,SemiprimeD1RecoveryStripBits.signed_value,h]
/-- Actual early canonical magnitude cache, physically produced before the Newton loop. -/
def magnitudeResidue (p:Nat) (n:SignedWord) (d:List Bool):List Bool:=
  (J.reduce p (corrected n.negative d n.magnitude)).bits
/-- Actual post-inverse signed residue: real negative-one product for negative sign, preserving full signed floor semantics. -/
def signedWord (p:Nat) (n:SignedWord) (d:List Bool):List Bool:=
  if n.negative then (J.mul p (SemiprimeD1OddInverseBits.negativeOne p).bits (magnitudeResidue p n d)).bits
  else magnitudeResidue p n d
/-- The real reduced-magnitude sign circuit has the same exact compact bytes as the old signed quotient circuit. -/
theorem signed_quotient (p:Nat) (n:SignedWord) (d:List Bool):
    signedWord p n d=(Old.signed p (quotient n d)).bits:=by
  cases hn:n.negative with
  | false=>simp only [signedWord,hn,Bool.false_eq_true,ite_false,Old.signed,quotient,magnitudeResidue]
  | true=>
    simp only [signedWord,hn,ite_true,Old.signed,quotient,magnitudeResidue]
    exact mul_reduce_right p _ _
/-- Actual signed cache agrees byte for byte with the ORIGINAL full floorSignedBits result after modular reduction. -/
theorem signed_original (p:Nat) (n:SignedWord) (d:List Bool):
    signedWord p n d=(Old.signed p (SemiprimeBitIndexClipping.floorSignedBits n (Old.acquire d).content).word).bits:=
  (signed_quotient p n d).trans (signed_congr p _ _ (quotient_floor_original n d))
/-- Proof-side description of the actual literal inverse/sign/final-product result. -/
def output (p:Nat) (n:SignedWord) (d:List Bool):List Bool:=
  (J.mul p (signedWord p n d) (SemiprimeD1OddInverseBits.inverse p (odd d)).bits).bits
/-- Exact ORIGINAL RecoveryStripBits.finish word; no native clock or encoded answer is used by the source. -/
theorem output_original (p:Nat) (n:SignedWord) (d:List Bool):output p n d=(Old.finish p n d).bits:=by
  simp only [output,Old.finish,(acquire_words d).2,signed_original]
/-- The resulting original residue is exact for every positive binary denominator and arbitrary signed numerator. -/
theorem residue_original (p:Nat) (n:SignedWord) (d:List Bool) (hd:0<bitValue d):
    (bitValue (output p n d):ZMod (2^p))=SemiprimeD1IntegerRecoveryResidue.finish p
      {numerator:=n.value,denominator:=bitValue d,arithmetic:=0,digitReads:=0}:=by
  rw [output_original]
  exact SemiprimeD1RecoveryStripBits.finish_value p n d hd
/-- Final byte width and compactness are intrinsic consequences of the actual final modular product. -/
theorem output_good (p:Nat) (n:SignedWord) (d:List Bool):
    (output p n d).length≤p ∧SemiprimeSourceCompactBits.Compact (output p n d):=
  ⟨J.mul_length _ _ _,J.mul_compact _ _ _⟩
end RiemannGaussian.SemiprimeD1StackRecoveryFinishResidue
