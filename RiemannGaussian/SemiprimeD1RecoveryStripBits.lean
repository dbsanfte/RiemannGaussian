/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryIntegerBits
import RiemannGaussian.SemiprimeD1OddInverseBounds
import RiemannGaussian.SemiprimeD1IntegerRecoveryResidue

/-! # Physical cancellation of the actual denominator's dyadic content
Only actual low bits are inspected. No native valuation, large integer quotient,
canonical rational field, or native inverse is encoded into the output.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryStripBits
open SemiprimeBitArithmetic SemiprimeBitDivision
open SemiprimeD1RecoveryIntegerBits

/-- Actual copied odd suffix and the literal shifted-one content word. -/
structure Report where
  /-- Physical power-of-two word. -/
  content : List Bool
  /-- Actual denominator suffix, copied at the first one. -/
  odd : List Bool
  /-- Inspected, copied and newly allocated payload cells. -/
  clock : ℕ

/-- Strip actual low zero bits, constructing the content without decoding it. -/
def acquire : List Bool → Report
  | [] => ⟨[true],[],3⟩
  | false::xs =>
    let tail:=acquire xs
    ⟨false::tail.content,tail.odd,tail.clock+4⟩
  | true::xs =>
    let copied:=fitBits (true::xs) (true::xs)
    ⟨[true],copied.bits,bitCost copied+3⟩

/-- The physical content/suffix factorization is exact even for zero inputs. -/
theorem factor (bits : List Bool) :
    bitValue bits=bitValue (acquire bits).content*bitValue (acquire bits).odd := by
  induction bits with
  | nil => simp [acquire,bitValue]
  | cons b xs ih =>
    cases b with
    | false => simpa [acquire,bitValue,bitNat,Nat.mul_assoc] using ih
    | true =>
      have hc:=fitBits_value (bitValue_lt_width (true::xs))
      simpa [acquire,bitValue,bitNat] using hc.symm

/-- The constructed content is literally a power of two. -/
theorem content_power (bits : List Bool) : ∃ v : ℕ, bitValue (acquire bits).content=2^v := by
  induction bits with
  | nil => exact ⟨0,by simp [acquire,bitValue,bitNat]⟩
  | cons b xs ih =>
    cases b with
    | false =>
      rcases ih with ⟨v,hv⟩
      refine ⟨v+1,?_⟩
      simp [acquire,bitValue,bitNat,hv,pow_succ,Nat.mul_comm]
    | true => exact ⟨0,by simp [acquire,bitValue,bitNat]⟩

/-- Positive original denominators produce an odd actual copied suffix. -/
theorem odd_suffix (bits : List Bool) (h : 0 < bitValue bits) :
    Odd (bitValue (acquire bits).odd) := by
  induction bits with
  | nil => simp [bitValue] at h
  | cons b xs ih =>
    cases b with
    | false =>
      have hx : 0 < bitValue xs := by simpa [bitValue,bitNat] using h
      exact ih hx
    | true =>
      have hc:=fitBits_value (bitValue_lt_width (true::xs))
      change Odd (bitValue (fitBits (true::xs) (true::xs)).bits)
      rw [hc]
      exact ⟨bitValue xs,by simp [bitValue,bitNat]; omega⟩

/-- The physical shifted-one word is exactly the original maximal dyadic content. -/
theorem content_value (bits : List Bool) (h : 0 < bitValue bits) :
    bitValue (acquire bits).content=SemiprimeD1IntegerRecoveryResidue.content (bitValue bits) := by
  rcases content_power bits with ⟨v,hv⟩
  have ho:=odd_suffix bits h
  have hn : ¬2 ∣ bitValue (acquire bits).odd := by
    simpa only [←even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr ho)
  have hz:=padicValNat.eq_zero_of_not_dvd hn
  have hp : 0 < bitValue (acquire bits).odd := by
    have hf:=factor bits
    omega
  have hf:=factor bits
  rw [hv] at hf
  have hval : padicValNat 2 (bitValue bits)=v := by
    rw [hf,padicValNat.mul (by positivity) (by omega),padicValNat.prime_pow,hz,Nat.add_zero]
  simpa only [SemiprimeD1IntegerRecoveryResidue.content,hval] using hv

/-- The copied odd suffix equals the exact original integer cofactor. -/
theorem odd_value (bits : List Bool) (h : 0 < bitValue bits) :
    bitValue (acquire bits).odd=bitValue bits /
      SemiprimeD1IntegerRecoveryResidue.content (bitValue bits) := by
  have hf:=factor bits
  have hc:=content_value bits h
  have hp:0<bitValue (acquire bits).content := by
    rcases content_power bits with ⟨v,hv⟩
    rw [hv]; positivity
  rw [←hc,hf,Nat.mul_div_right _ hp]

/-- Neither returned word exceeds the actual input size plus one. -/
theorem lengths (bits : List Bool) :
    (acquire bits).content.length ≤ bits.length+1 ∧ (acquire bits).odd.length ≤ bits.length := by
  induction bits with
  | nil => simp [acquire]
  | cons b xs ih =>
    cases b with
    | false =>
      simp only [acquire,List.length_cons]
      omega
    | true =>
      have hc:=(fitBits_counts (true::xs) (true::xs)).1
      simp only [acquire,List.length_cons,List.length_nil] at *
      omega

/-- All actual trailing-zero tests, shifts and suffix-copy cells are paid. -/
theorem acquire_clock (bits : List Bool) : (acquire bits).clock ≤ 8*bits.length+10 := by
  induction bits with
  | nil => simp [acquire]
  | cons b xs ih =>
    cases b with
    | false => simp only [acquire,List.length_cons]; omega
    | true =>
      have hc:=fitBits_cost (true::xs) (true::xs)
      simp only [acquire,List.length_cons] at *
      omega

/-- Reduce the actual signed magnitude, handling the stored Boolean sign. -/
def signed (p : ℕ) (x : SemiprimeBitIndexClipping.SignedWord) :
    SemiprimeSourceCompactBits.Report :=
  if x.negative then
    let negative:=SemiprimeD1OddInverseBits.negativeOne p
    let out:=SemiprimeD1JetScalarBits.mul p negative.bits x.magnitude
    ⟨out.bits,negative.clock+out.clock+3⟩
  else SemiprimeD1JetScalarBits.reduce p x.magnitude

/-- Signed modular reduction never decodes and reencodes the input integer. -/
theorem signed_value (p : ℕ) (x : SemiprimeBitIndexClipping.SignedWord) :
    (bitValue (signed p x).bits:ZMod (2^p))=(x.value:ZMod (2^p)) := by
  cases hx:x.negative with
  | false => simp [signed,hx,SemiprimeBitIndexClipping.SignedWord.value,
      SemiprimeD1JetScalarBits.reduce_value,ZMod.natCast_mod]
  | true =>
    simp only [signed,hx,ite_true,SemiprimeD1JetScalarBits.mul_zmod]
    change SemiprimeD1OddInverseBits.value p (SemiprimeD1OddInverseBits.negativeOne p).bits *
      (bitValue x.magnitude:ZMod (2^p)) = _
    rw [SemiprimeD1OddInverseBits.negativeOne_zmod]
    simp [SemiprimeBitIndexClipping.SignedWord.value,hx]

/-- Actual signed modular output is compact and bounded by the precision. -/
theorem signed_good (p : ℕ) (x : SemiprimeBitIndexClipping.SignedWord) :
    (signed p x).bits.length ≤ p ∧ SemiprimeSourceCompactBits.Compact (signed p x).bits := by
  cases hx:x.negative with
  | false => simpa only [signed,hx,Bool.false_eq_true,ite_false] using
      (And.intro (SemiprimeD1JetScalarBits.reduce_length p x.magnitude)
        (SemiprimeD1JetScalarBits.reduce_compact p x.magnitude))
  | true => simpa only [signed,hx,ite_true] using
      (And.intro (SemiprimeD1JetScalarBits.mul_length p
        (SemiprimeD1OddInverseBits.negativeOne p).bits x.magnitude)
        (SemiprimeD1JetScalarBits.mul_compact p
          (SemiprimeD1OddInverseBits.negativeOne p).bits x.magnitude))

/-- Full physical cancellation, floor quotient, odd inverse and residue product.
No native content, quotient, signed digits or inverse is supplied. -/
def finish (p : ℕ) (numerator : SemiprimeBitIndexClipping.SignedWord)
    (denominator : List Bool) : SemiprimeSourceCompactBits.Report :=
  let stripped:=acquire denominator
  let divided:=SemiprimeBitIndexClipping.floorSignedBits numerator stripped.content
  let inverse:=SemiprimeD1OddInverseBits.inverse p stripped.odd
  let reduced:=signed p divided.word
  let out:=SemiprimeD1JetScalarBits.mul p reduced.bits inverse.bits
  ⟨out.bits,stripped.clock+divided.clock+inverse.clock+reduced.clock+out.clock+8⟩

/-- The physically stripped final output is exactly the original recovery
fraction residue, including its actual maximal power-of-two cancellation. -/
theorem finish_value (p : ℕ) (numerator : SemiprimeBitIndexClipping.SignedWord)
    (denominator : List Bool) (hd : 0 < bitValue denominator) :
    (bitValue (finish p numerator denominator).bits:ZMod (2^p))=
      SemiprimeD1IntegerRecoveryResidue.finish p
        {numerator:=numerator.value,denominator:=bitValue denominator,arithmetic:=0,digitReads:=0} := by
  have hc:=content_value denominator hd
  have ho:=odd_value denominator hd
  have hi:=SemiprimeD1OddInverseBounds.inverse_eq_native p (acquire denominator).odd
    (odd_suffix denominator hd)
  have hq:=SemiprimeBitIndexClipping.floorSignedBits_value numerator (acquire denominator).content
  simp only [finish,SemiprimeD1JetScalarBits.mul_zmod,signed_value]
  change _ * SemiprimeD1OddInverseBits.value p _ = _
  rw [hi]
  simp only [SemiprimeD1OddInverseBits.value,hq,hc,ho,
    SemiprimeD1IntegerRecoveryResidue.finish,SemiprimeD1CrossingResidue.residue,
    SemiprimeD1IntegerRecoveryResidue.stripped,Int.cast_natCast]

/-- Actual final words are compact at the requested precision. -/
theorem finish_good (p : ℕ) (numerator : SemiprimeBitIndexClipping.SignedWord)
    (denominator : List Bool) :
    (finish p numerator denominator).bits.length ≤ p ∧
      SemiprimeSourceCompactBits.Compact (finish p numerator denominator).bits :=
  ⟨SemiprimeD1JetScalarBits.mul_length _ _ _,SemiprimeD1JetScalarBits.mul_compact _ _ _⟩

/-- Actual sign handling pays both the all-one word and modular product. -/
theorem signed_clock (p : ℕ) (x : SemiprimeBitIndexClipping.SignedWord) :
    (signed p x).clock ≤ 12*p*(p+x.magnitude.length+2)+10*p+20 := by
  have hm:=SemiprimeD1JetScalarBits.mul_clock p
    (SemiprimeD1OddInverseBits.negativeOne p).bits x.magnitude
  have hr:=SemiprimeD1JetScalarBits.reduce_clock p x.magnitude
  simp only [SemiprimeD1OddInverseBits.negativeOne,List.length_replicate] at hm
  cases hx:x.negative with
  | false => simpa only [signed,hx,Bool.false_eq_true,ite_false] using
      hr.trans (by omega : 9*p+5 ≤ 12*p*(p+x.magnitude.length+2)+10*p+20)
  | true =>
    simp only [signed,hx,ite_true,SemiprimeD1OddInverseBits.negativeOne]
    omega

/-- A closed polynomial in the actual integer store width and target precision. -/
def budget (p W : ℕ) : ℕ :=
  8*W+10+150*(W+2)^2+400*(p+1)^3+
    (12*p*(p+W+5)+10*p+20)+(12*p*(2*p+2)+9*p+9)+8

/-- Physical content stripping/floor division/sign/inverse/product has no native
large-integer or digit-extraction stage, and every retained report is bounded. -/
theorem finish_clock (p W : ℕ) (numerator : SemiprimeBitIndexClipping.SignedWord)
    (denominator : List Bool) (hn : numerator.magnitude.length ≤ W)
    (hd : denominator.length ≤ W) :
    (finish p numerator denominator).clock ≤ budget p W := by
  have hs:=acquire_clock denominator
  have hlen:=lengths denominator
  have hnum : numerator.magnitude.length ≤ W+1 := by omega
  have hden : (acquire denominator).content.length ≤ W+1 := by omega
  have hq:=SemiprimeBitIndexClipping.floorSignedBits_cost_width hnum hden
  have hi:=SemiprimeD1OddInverseBounds.inverse_clock p (acquire denominator).odd
  have hsign:=signed_clock p
    (SemiprimeBitIndexClipping.floorSignedBits numerator (acquire denominator).content).word
  have hsign' : (signed p
      (SemiprimeBitIndexClipping.floorSignedBits numerator (acquire denominator).content).word).clock ≤
        12*p*(p+W+5)+10*p+20 := by
    have hb : p+(SemiprimeBitIndexClipping.floorSignedBits numerator
        (acquire denominator).content).word.magnitude.length+2 ≤ p+W+5 := by omega
    have hm:=Nat.mul_le_mul_left (12*p) hb
    omega
  have hm:=SemiprimeD1JetScalarBits.mul_clock p
    (signed p (SemiprimeBitIndexClipping.floorSignedBits numerator (acquire denominator).content).word).bits
    (SemiprimeD1OddInverseBits.inverse p (acquire denominator).odd).bits
  have hl1:=(signed_good p
    (SemiprimeBitIndexClipping.floorSignedBits numerator (acquire denominator).content).word).1
  have hl2:=(SemiprimeD1OddInverseBits.inverse_good p (acquire denominator).odd).1
  have hm' : 12*(signed p
      (SemiprimeBitIndexClipping.floorSignedBits numerator (acquire denominator).content).word).bits.length*
      ((signed p (SemiprimeBitIndexClipping.floorSignedBits numerator
        (acquire denominator).content).word).bits.length+
        (SemiprimeD1OddInverseBits.inverse p (acquire denominator).odd).bits.length+2) ≤
      12*p*(2*p+2) := by gcongr; omega
  simp only [finish,budget]
  nlinarith only [hs,hd,hq.1,hi,hsign',hm,hm']

end RiemannGaussian.SemiprimeD1RecoveryStripBits
