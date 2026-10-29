/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryStripBits
import RiemannGaussian.SemiprimeD1RadixOperandBits
import RiemannGaussian.SemiprimeD1WireKernelFactors
import RiemannGaussian.SemiprimeBitIndexGeometry

/-! # Physical normalized original linear factors
Subtraction, low-bit stripping and unsigned division acquire the factor. Native
valuations and exact integer quotients occur only in the correctness statement.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1NormalizedLinearBits
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitIndexClipping
open SemiprimeBitIndexGeometry SemiprimeBitFermatArithmetic
open SemiprimeD1RecoveryIntegerBits SemiprimeD1WireKernelFactors

/-- Acquired content, signed constant, slope and retained physical work. -/
structure Run where
  /-- Literal dyadic content word. -/
  content : List Bool
  /-- Signed stripped difference. -/
  constant : SignedWord
  /-- Exact alpha/content quotient word. -/
  slope : List Bool
  /-- All arithmetic and allocation reports. -/
  clock : ℕ

/-- Actual shifted-one alpha, including radix allocation. -/
def alpha (k : ℕ) : SemiprimeD1RadixOperandBits.Run :=
  let shifted:=shiftTemplateBits (List.replicate k false) [true]
  ⟨shifted.bits,bitCost shifted+3*k+2⟩

/-- Alpha has its original exact value. -/
theorem alpha_value (k : ℕ) : bitValue (alpha k).bits=2^k := by
  have h:bitValue [true]=1:=rfl
  simpa only [alpha,List.length_replicate,h,Nat.mul_one] using
    (shiftTemplateBits_exact (List.replicate k false) [true]).1

/-- Compute the original factor using physical words only. -/
def acquire (k : ℕ) (j q : List Bool) : Run :=
  let a:=alpha k
  let delta:=subSignedBits (positive j) (positive q)
  let test:=nonzeroBits delta.word.magnitude
  if test.nonzero then
    let stripped:=SemiprimeD1RecoveryStripBits.acquire delta.word.magnitude
    let quotient:=divideBits a.bits stripped.content
    ⟨stripped.content,⟨delta.word.negative,stripped.odd⟩,quotient.quotient,
      a.clock+delta.clock+test.clock+stripped.clock+quotient.clock+8⟩
  else
    ⟨a.bits,positive [],[true],a.clock+delta.clock+test.clock+8⟩

/-- Exact signed subtraction at the original indices. -/
theorem difference_value (j q : List Bool) :
    (subSignedBits (positive j) (positive q)).word.value=
      difference (bitValue j) (bitValue q) := by
  exact subSignedBits_value (positive j) (positive q)

/-- The acquired content matches the original normalization exponent. -/
theorem acquire_content (k : ℕ) (j q : List Bool) :
    bitValue (acquire k j q).content=2^factorOrder k (bitValue j) (bitValue q) := by
  have hv:=difference_value j q
  have ha:=signedWord_natAbs (subSignedBits (positive j) (positive q)).word
  dsimp only [acquire]
  split
  next h =>
    have hp:= (nonzeroBits_correct _).mp h
    rw [SemiprimeD1RecoveryStripBits.content_value _ hp]
    unfold SemiprimeD1IntegerRecoveryResidue.content
    rw [←ha,hv]
    have hn:bitValue q≠bitValue j:=by
      intro he
      simp only [difference,he,sub_self] at hv ha
      omega
    simp only [factorOrder,ite_eq_right hn,padicValInt]
  next h =>
    have hz:bitValue (subSignedBits (positive j) (positive q)).word.magnitude=0:=by
      have hh:=nonzeroBits_correct (subSignedBits (positive j) (positive q)).word.magnitude
      cases hb:(nonzeroBits (subSignedBits (positive j) (positive q)).word.magnitude).nonzero
      · have :¬0<bitValue (subSignedBits (positive j) (positive q)).word.magnitude:=by
          intro hp; have ht:=hh.mpr hp; simp [hb] at ht
        omega
      · contradiction
    have he:bitValue q=bitValue j:=by
      rw [hz] at ha
      have hh:Int.natAbs (difference (bitValue j) (bitValue q))=0:=by simpa [hv] using ha
      have :=Int.natAbs_eq_zero.mp hh
      unfold difference at this
      omega
    simpa only [factorOrder,ite_eq_left he] using alpha_value k
/-- The acquired signed constant reconstructs the actual signed difference. -/
theorem acquire_reconstruct (k : ℕ) (j q : List Bool) :
    (acquire k j q).constant.value*(bitValue (acquire k j q).content:ℤ)=
      difference (bitValue j) (bitValue q) := by
  have hv:=difference_value j q
  have ha:=signedWord_natAbs (subSignedBits (positive j) (positive q)).word
  dsimp only [acquire]
  split
  next h =>
    have hf:=SemiprimeD1RecoveryStripBits.factor
      (subSignedBits (positive j) (positive q)).word.magnitude
    have hi:(bitValue (subSignedBits (positive j) (positive q)).word.magnitude:ℤ)=
        (bitValue (SemiprimeD1RecoveryStripBits.acquire
          (subSignedBits (positive j) (positive q)).word.magnitude).content:ℤ)*
        (bitValue (SemiprimeD1RecoveryStripBits.acquire
          (subSignedBits (positive j) (positive q)).word.magnitude).odd:ℤ):=by
      exact_mod_cast hf
    rw [←hv]
    cases hs:(subSignedBits (positive j) (positive q)).word.negative <;>
      simp only [SignedWord.value,hs,Bool.false_eq_true,ite_false,ite_true] <;>
      nlinarith only [hi]
  next h =>
    have hh:=nonzeroBits_correct (subSignedBits (positive j) (positive q)).word.magnitude
    have hz:bitValue (subSignedBits (positive j) (positive q)).word.magnitude=0:=by
      by_contra hn
      have hp:0<bitValue (subSignedBits (positive j) (positive q)).word.magnitude:=by omega
      exact h (hh.mpr hp)
    have hd:difference (bitValue j) (bitValue q)=0:=by
      apply Int.natAbs_eq_zero.mp
      rw [←hv,ha,hz]
    simp only [positive,SignedWord.value,Bool.false_eq_true,ite_false,bitValue,
      Int.natCast_zero,zero_mul,hd]

/-- The physical constant is the original normalized signed coefficient. -/
theorem acquire_constant (k : ℕ) (j q : List Bool) :
    (acquire k j q).constant.value=(normalizedFactor k (bitValue j) (bitValue q)).constant := by
  have h:=acquire_reconstruct k j q
  rw [acquire_content] at h
  have hc:=normalized_constant k (bitValue j) (bitValue q)
  have hp:(2:ℤ)^factorOrder k (bitValue j) (bitValue q)≠0:=by positivity
  have hcast:((2^factorOrder k (bitValue j) (bitValue q):ℕ):ℤ)=
      (2:ℤ)^factorOrder k (bitValue j) (bitValue q):=by norm_cast
  rw [hcast] at h
  exact mul_right_cancel₀ hp (h.trans hc.symm)

/-- The original range guards derive exact slope division, without quotient advice. -/
theorem acquire_slope (k : ℕ) (j q : List Bool)
    (hj:bitValue j<2^k) (hq:bitValue q<2^k) :
    (bitValue (acquire k j q).slope:ℤ)=
      (normalizedFactor k (bitValue j) (bitValue q)).slope := by
  have hcontent:=acquire_content k j q
  have hdiv:=factorOrder_dvd_alpha k (bitValue j) (bitValue q) hj hq
  have hd:(2^factorOrder k (bitValue j) (bitValue q):ℕ)∣2^k:=by
    exact_mod_cast hdiv
  have hs:=normalized_slope k (bitValue j) (bitValue q) hj hq
  dsimp only [acquire] at hcontent ⊢
  split
  next h =>
    simp only [ite_eq_left h] at hcontent
    have hv:bitValue (divideBits (alpha k).bits
        (SemiprimeD1RecoveryStripBits.acquire
          (subSignedBits (positive j) (positive q)).word.magnitude).content).quotient=
        2^k/2^factorOrder k (bitValue j) (bitValue q):=by
      rw [(divideBits_correct _ _).1,alpha_value,hcontent]
    rw [hv]
    have he:(2^k/2^factorOrder k (bitValue j) (bitValue q):ℕ)*
        2^factorOrder k (bitValue j) (bitValue q)=2^k:=Nat.div_mul_cancel hd
    have hei:((2^k/2^factorOrder k (bitValue j) (bitValue q):ℕ):ℤ)*
        (2:ℤ)^factorOrder k (bitValue j) (bitValue q)=(2:ℤ)^k:=by exact_mod_cast he
    exact mul_right_cancel₀ (by positivity : (2:ℤ)^factorOrder k (bitValue j) (bitValue q)≠0)
      (hei.trans hs.symm)
  next h =>
    simp only [ite_eq_right h] at hcontent
    have he:factorOrder k (bitValue j) (bitValue q)=k:=by
      rw [alpha_value] at hcontent
      exact (Nat.pow_right_injective (by decide : 1<(2:ℕ))) hcontent.symm
    rw [he] at hs
    have hp:(2:ℤ)^k≠0:=by positivity
    have hh:(1:ℤ)*(2:ℤ)^k=(normalizedFactor k (bitValue j) (bitValue q)).slope*(2:ℤ)^k:=by
      simpa only [one_mul] using hs.symm
    exact mul_right_cancel₀ hp hh
/-- Genuine alpha width, including its high one. -/
theorem alpha_length (k : ℕ) : (alpha k).bits.length=k+1 := by
  simpa only [alpha,List.length_replicate,List.length_cons,List.length_nil] using
    (shiftTemplateBits_exact (List.replicate k false) [true]).2.1

/-- All alpha construction work is retained. -/
theorem alpha_clock (k : ℕ) : (alpha k).clock=6*k+3 := by
  have h:=(shiftTemplateBits_exact (List.replicate k false) [true]).2.2
  simp only [List.length_replicate] at h
  dsimp only [alpha]
  rw [h]
  omega

/-- Original physical input sizes derive every output width; no fit advice. -/
theorem acquire_width (k W : ℕ) (j q : List Bool)
    (hj:j.length≤W) (hq:q.length≤W) :
    (acquire k j q).content.length≤k+W+2 ∧
    (acquire k j q).constant.magnitude.length≤W+1 ∧
    (acquire k j q).slope.length≤k+1 := by
  have hw:=(subSignedBits_cost_width (left:=positive j) (right:=positive q) hj hq).2
  have hs:=SemiprimeD1RecoveryStripBits.lengths
    (subSignedBits (positive j) (positive q)).word.magnitude
  dsimp only [acquire]
  split
  next h =>
    rcases SemiprimeD1RecoveryStripBits.content_power
        (subSignedBits (positive j) (positive q)).word.magnitude with ⟨v,hv⟩
    have hp:0<bitValue (SemiprimeD1RecoveryStripBits.acquire
        (subSignedBits (positive j) (positive q)).word.magnitude).content:=by rw [hv]; positivity
    have hd:=(divideBits_widths (xs:=(alpha k).bits) hp).2
    rw [alpha_length] at hd
    dsimp only
    exact ⟨by omega,by omega,by omega⟩
  next h =>
    simp only [alpha_length,positive,List.length_nil,List.length_cons]
    omega

/-- Explicit polynomial physical arithmetic/list budget. -/
def budget (k W : ℕ) : ℕ :=
  6*k+3+41*(W+1)+(3*(W+1)+1)+(8*(W+1)+10)+
    (k+1)*(16*(W+2)+20)+7*(W+2)+4+8

/-- Complete executed report bound from original input widths only. -/
theorem acquire_clock (k W : ℕ) (j q : List Bool)
    (hj:j.length≤W) (hq:q.length≤W) :
    (acquire k j q).clock≤budget k W := by
  have hdelta:=subSignedBits_cost_width (left:=positive j) (right:=positive q) hj hq
  have ht:=nonzeroBits_cost (subSignedBits (positive j) (positive q)).word.magnitude
  have hs:=SemiprimeD1RecoveryStripBits.acquire_clock
    (subSignedBits (positive j) (positive q)).word.magnitude
  have hl:=SemiprimeD1RecoveryStripBits.lengths
    (subSignedBits (positive j) (positive q)).word.magnitude
  have hd:=divideBits_cost (alpha k).bits (SemiprimeD1RecoveryStripBits.acquire
    (subSignedBits (positive j) (positive q)).word.magnitude).content
  rw [alpha_length] at hd
  have hbound:(k+1)*(16*(SemiprimeD1RecoveryStripBits.acquire
      (subSignedBits (positive j) (positive q)).word.magnitude).content.length+20)≤
      (k+1)*(16*(W+2)+20):=by
    apply Nat.mul_le_mul_left
    omega
  dsimp only [acquire]
  split <;> dsimp only <;> rw [alpha_clock] <;> unfold budget <;> omega
end RiemannGaussian.SemiprimeD1NormalizedLinearBits
