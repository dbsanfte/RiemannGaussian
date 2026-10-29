/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryStripBits
import RiemannGaussian.SemiprimeD1JetKernelBitsBounds
import RiemannGaussian.SemiprimeSourceCompactWordIds

/-! # Dense jet constants from actual physical signed source words
Physical low-prefix reduction, sign arithmetic and copied dense allocation
consume literal bytes. No decoded native integer or signed digit extraction
produces the runtime vector. Value/byte agreement with the old integer encoder
is a proof-side bridge; its clock is not transferred to this new program.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1JetWordSourceBits
open SemiprimeBitArithmetic SemiprimeBitIndexClipping SemiprimeD1JetAxes
open SemiprimeD1JetInterpretation SemiprimeD1JetPolynomialBits
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- Original integer encoder is intrinsically compact. This is used only to
upgrade proved residue agreement to literal byte agreement below. -/
theorem integer_compact (p : ℕ) (z : ℤ) :
    SemiprimeSourceCompactBits.Compact (SemiprimeD1JetKernelBits.integer p z).bits := by
  unfold SemiprimeD1JetKernelBits.integer
  split
  · exact SemiprimeD1JetScalarBits.mul_compact _ _ _
  · exact SemiprimeSourceCompactBits.trim_compact _

/-- Physical signed-word reduction agrees literally with the old canonical
integer encoding when their proof-side integer interpretations agree. -/
theorem signed_words_eq_integer (p : ℕ) (x : SignedWord) (z : ℤ) (hx : x.value=z) :
    (SemiprimeD1RecoveryStripBits.signed p x).bits=(SemiprimeD1JetKernelBits.integer p z).bits := by
  have hs := SemiprimeD1RecoveryStripBits.signed_good p x
  have ho := SemiprimeD1JetKernelBitsBounds.integer_length p z
  have hc := integer_compact p z
  have hleft : bitValue (SemiprimeD1RecoveryStripBits.signed p x).bits < 2^p :=
    (bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hs.1)
  have hright : bitValue (SemiprimeD1JetKernelBits.integer p z).bits < 2^p :=
    (bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ho)
  let _ : NeZero (2^p) := ⟨by positivity⟩
  have hr := SemiprimeD1RecoveryStripBits.signed_value p x
  rw [hx] at hr
  have he := congrArg (fun y : ZMod (2^p) => y.val)
    (hr.trans (SemiprimeD1JetKernelBits.integer_value p z).symm)
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hleft,Nat.mod_eq_of_lt hright] at he
  exact SemiprimeSourceCompactWordIds.compact_value_injective _ _ hs.2 hc he

/-- Actual byte-to-jet constant acquisition; word interpretation is never used
by this executed function. Every source bit and allocated coordinate is paid. -/
def constant (ctx : Context) (word : SignedWord) : JetRun :=
  let source := SemiprimeD1RecoveryStripBits.signed ctx.precision word
  let out := scalar ctx source.bits
  ⟨out.words,source.clock+out.clock+3⟩

/-- The actual new dense vector is the signed original-word constant image. -/
theorem constant_value (ctx : Context) (word : SignedWord) (hpos : ctx.Positive) :
    interpret ctx (constant ctx word).words=
      SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)
        (word.value:ZMod (2^ctx.precision)) := by
  change interpret ctx (scalar ctx (SemiprimeD1RecoveryStripBits.signed ctx.precision word).bits).words=_
  rw [scalar_value ctx _ hpos,SemiprimeD1RecoveryStripBits.signed_value]

/-- Literal byte compatibility with the original dense integer encoder, with
no equality or transfer of their distinct source-acquisition reports. -/
theorem constant_words_eq_integerVector (ctx : Context) (word : SignedWord) (z : ℤ)
    (hz : word.value=z) :
    (constant ctx word).words=(SemiprimeD1JetKernelBits.integerVector ctx z).words := by
  dsimp only [constant,SemiprimeD1JetKernelBits.integerVector]
  rw [signed_words_eq_integer ctx.precision word z hz]

/-- Actual current vector rank and scalar width are derived from physical reduction. -/
theorem constant_good (ctx : Context) (word : SignedWord) :
    SemiprimeD1JetAffineCoefficientBounds.Good ctx (constant ctx word).words := by
  exact ⟨SemiprimeD1JetPolynomialBitsBounds.scalar_shape ctx _,
    SemiprimeD1JetPolynomialBitsBounds.scalar_bounded ctx _ _
      (SemiprimeD1RecoveryStripBits.signed_good ctx.precision word).1⟩

/-- Complete actual source reduction and copied dense allocation have a fixed
polynomial bit report in the supplied physical width, precision and rank. -/
theorem constant_clock (ctx : Context) (word : SignedWord) :
    (constant ctx word).clock ≤
      12*ctx.precision*(ctx.precision+word.magnitude.length+2)+
        13*ctx.precision+3*ctx.rank+27 := by
  have hs := SemiprimeD1RecoveryStripBits.signed_clock ctx.precision word
  have hw := (SemiprimeD1RecoveryStripBits.signed_good ctx.precision word).1
  have hc := SemiprimeD1JetPolynomialBitsBounds.scalar_clock ctx
    (SemiprimeD1RecoveryStripBits.signed ctx.precision word).bits
  change (SemiprimeD1RecoveryStripBits.signed ctx.precision word).clock+
    (scalar ctx (SemiprimeD1RecoveryStripBits.signed ctx.precision word).bits).clock+3 ≤ _
  omega

end RiemannGaussian.SemiprimeD1JetWordSourceBits
