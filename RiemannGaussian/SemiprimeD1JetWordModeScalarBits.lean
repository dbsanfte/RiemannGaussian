/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetWordSourceBits
import RiemannGaussian.SemiprimeD1JetModeBitsBounds
import RiemannGaussian.SemiprimeD1KernelEntryBits

/-! # Actual word-supplied crossing inverse caches and steps
Only acquired signed constants, unsigned slopes and content words drive the
scalar arithmetic. Original normalized factors and valuations specify outputs
on the proof side, never produce executed coefficient or step words.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1JetWordModeScalarBits
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitIndexClipping
open SemiprimeD1RecoveryIntegerBits SemiprimeD1JetModeBits
open SemiprimeD1WireKernelOriginal SemiprimeD1WireKernelFactors

/-- Cached physical inverse coefficients from actual constant/slope words. -/
def inverseCache (p : ℕ) (constant : SignedWord) (slope : List Bool) : Cache :=
  let c:=SemiprimeD1RecoveryStripBits.signed p constant
  let s:=SemiprimeD1RecoveryStripBits.signed p (positive slope)
  let inverse:=SemiprimeD1OddInverseBits.inverse p c.bits
  let negative:=SemiprimeD1OddInverseBits.negativeOne p
  let opposite:=SemiprimeD1JetScalarBits.mul p negative.bits s.bits
  let ratio:=SemiprimeD1JetScalarBits.mul p opposite.bits inverse.bits
  let out:=geometric p ratio.bits inverse.bits p
  ⟨out.words,c.clock+s.clock+inverse.clock+negative.clock+opposite.clock+ratio.clock+out.clock+15⟩

/-- Literal cache bytes agree with the frozen original cache, without clock transfer. -/
theorem inverseCache_words (p : ℕ) (constant : SignedWord) (slope : List Bool) :
    (inverseCache p constant slope).words=
      (SemiprimeD1JetModeBits.inverseCache p constant.value (bitValue slope)).words := by
  dsimp only [inverseCache,SemiprimeD1JetModeBits.inverseCache]
  rw [SemiprimeD1JetWordSourceBits.signed_words_eq_integer p constant constant.value rfl,
    SemiprimeD1JetWordSourceBits.signed_words_eq_integer p (positive slope) (bitValue slope) rfl]

/-- Genuine cache length is the requested finite precision. -/
theorem inverseCache_length (p : ℕ) (constant : SignedWord) (slope : List Bool) :
    (inverseCache p constant slope).words.length=p := by
  rw [inverseCache_words]
  exact SemiprimeD1JetModeBits.inverseCache_length _ _ _

/-- Every acquired cache word has physical target precision width. -/
theorem inverseCache_bounded (p : ℕ) (constant : SignedWord) (slope : List Bool) :
    ∀w∈(inverseCache p constant slope).words,w.length≤p := by
  rw [inverseCache_words]
  exact SemiprimeD1JetModeBitsBounds.inverseCache_bounded _ _ _

/-- Divide the original step alpha by acquired content, clamping actual zero to one. -/
def step (i : ℕ) (content : List Bool) : SemiprimeSourceCompactBits.Report :=
  let a:=SemiprimeD1NormalizedLinearBits.alpha (i+1)
  let quotient:=divideBits a.bits content
  let test:=nonzeroBits quotient.quotient
  ⟨if test.nonzero then quotient.quotient else [true],
    a.clock+quotient.clock+test.clock+5⟩

/-- Exact natural power quotient with saturation at one. -/
theorem saturated_power (n v : ℕ) :
    (if 0<2^n/2^v then 2^n/2^v else 1)=2^(n-v) := by
  by_cases hv:v≤n
  · have he:n=v+(n-v):=by omega
    have hq:(2^n/2^v:ℕ)=2^(n-v):=by
      conv_lhs => rw [he,pow_add]
      exact Nat.mul_div_right _ (by positivity)
    rw [hq,ite_eq_left (by positivity)]
  · have hn:n<v:=by omega
    have hp:(2:ℕ)^n<2^v:=(Nat.pow_lt_pow_iff_right (by decide : 1<(2:ℕ))).mpr hn
    rw [Nat.div_eq_of_lt hp]
    simp only [Nat.lt_irrefl,ite_false,Nat.sub_eq_zero_of_le (by omega : n≤v),pow_zero]

/-- The executed step is the original truncated-exponent power, without exponent advice. -/
theorem step_value (i v : ℕ) (content : List Bool) (hc:bitValue content=2^v) :
    bitValue (step i content).bits=2^(i+1-v) := by
  have hq:(bitValue (divideBits (SemiprimeD1NormalizedLinearBits.alpha (i+1)).bits
      content).quotient)=2^(i+1)/2^v:=by
    rw [(divideBits_correct _ _).1,SemiprimeD1NormalizedLinearBits.alpha_value,hc]
  dsimp only [step]
  split
  next ht =>
    have hp:0<2^(i+1)/2^v:=by
      rw [←hq]
      exact (nonzeroBits_correct _).mp ht
    have hs:=saturated_power (i+1) v
    rw [ite_eq_left hp] at hs
    exact hq.trans hs
  next ht =>
    have hz:¬0<2^(i+1)/2^v:=by
      intro hp
      rw [←hq] at hp
      exact ht ((nonzeroBits_correct _).mpr hp)
    have hs:=saturated_power (i+1) v
    rw [ite_eq_right hz] at hs
    exact hs

/-- Scalar cache, acquired cancelled factor and physical crossing step. -/
structure Run where
  /-- Actual cancelled normalized factor words. -/
  factor : SemiprimeD1NormalizedLinearBits.Run
  /-- Actual acquired inverse coefficients. -/
  cache : Cache
  /-- Physical step power. -/
  step : List Bool
  /-- Every digit, normalization, inverse/cache and step report. -/
  clock : ℕ

/-- Actual original-input scalar mode data, with no supplied normalized factor or step. -/
def acquireOriginal (p a i : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a)) : Run :=
  let j:=SemiprimeEncodedRowSelection.digits (a+1) t.val
  let d:=SemiprimeEncodedRowSelection.digits (a+1) (displacement a x y₀).val
  let factor:=SemiprimeD1NormalizedLinearBits.acquire (a+1) j.bits d.bits
  let cache:=inverseCache p factor.constant factor.slope
  let tile:=step i factor.content
  ⟨factor,cache,tile.bits,j.work+d.work+factor.clock+cache.clock+tile.clock+8⟩

/-- Original acquired cancelled factor is exactly the original normalized linear data. -/
theorem acquire_factor (p a i : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a)) :
    SemiprimeD1KernelEntryBits.linear (acquireOriginal p a i t x y₀).factor=
      normalizedFactor (a+1) t.val (displacement a x y₀).val := by
  dsimp only [acquireOriginal]
  rw [SemiprimeD1KernelEntryBits.linear_value]
  · rw [SemiprimeEncodedRowSelection.digits_value (a+1) t.val t.isLt,
      SemiprimeEncodedRowSelection.digits_value (a+1) (displacement a x y₀).val
        (displacement a x y₀).isLt]
  · rw [SemiprimeEncodedRowSelection.digits_value (a+1) t.val t.isLt]
    exact t.isLt
  · rw [SemiprimeEncodedRowSelection.digits_value (a+1) (displacement a x y₀).val
      (displacement a x y₀).isLt]
    exact (displacement a x y₀).isLt

/-- Original inverse-cache bytes match the original normalized-factor cache exactly. -/
theorem acquire_cache_words (p a i : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a)) :
    (acquireOriginal p a i t x y₀).cache.words=
      (SemiprimeD1JetModeBits.inverseCache p
        (normalizedFactor (a+1) t.val (displacement a x y₀).val).constant
        (normalizedFactor (a+1) t.val (displacement a x y₀).val).slope).words := by
  have hf:=acquire_factor p a i t x y₀
  change (inverseCache p (acquireOriginal p a i t x y₀).factor.constant
    (acquireOriginal p a i t x y₀).factor.slope).words=_
  rw [inverseCache_words]
  change (SemiprimeD1JetModeBits.inverseCache p
    (SemiprimeD1KernelEntryBits.linear (acquireOriginal p a i t x y₀).factor).constant
    (SemiprimeD1KernelEntryBits.linear (acquireOriginal p a i t x y₀).factor).slope).words=_
  rw [hf]

/-- Original step value is acquired without a runtime valuation or exponent. -/
theorem acquire_step_value (p a i : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a)) :
    (bitValue (acquireOriginal p a i t x y₀).step:ℤ)=
      SemiprimeD1CrossingExpansion.step (a+1) i t.val (displacement a x y₀).val := by
  have hc:=SemiprimeD1NormalizedLinearBits.acquire_content (a+1)
    (SemiprimeEncodedRowSelection.digits (a+1) t.val).bits
    (SemiprimeEncodedRowSelection.digits (a+1) (displacement a x y₀).val).bits
  rw [SemiprimeEncodedRowSelection.digits_value (a+1) t.val t.isLt,
    SemiprimeEncodedRowSelection.digits_value (a+1) (displacement a x y₀).val
      (displacement a x y₀).isLt] at hc
  have hs:=step_value i _ _ hc
  unfold SemiprimeD1CrossingExpansion.step
  change (bitValue (step i _).bits:ℤ)=_
  exact_mod_cast hs
end RiemannGaussian.SemiprimeD1JetWordModeScalarBits
