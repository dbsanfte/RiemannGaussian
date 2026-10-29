/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetWordModeScalarBits

/-! # Original physical scalar mode acquisition bounds
The new reduction/cache clocks are bounded directly. Literal compatibility
with the old cache does not transfer or erase either acquisition report.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1JetWordModeScalarBounds
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitIndexClipping
open SemiprimeD1RecoveryIntegerBits SemiprimeD1JetModeBits
open SemiprimeD1WireKernelOriginal

/-- Finite physical inverse-cache budget from precision and original word width. -/
def inverseBudget (p W : ℕ) : ℕ :=
  2*(12*p*(p+W+2)+10*p+20)+400*(p+1)^3+p+2+100*(p+1)^2+
    p*SemiprimeD1JetModeBitsBounds.geometricStage p+16

/-- Every actual source reduction, odd inversion and cached geometric step is paid. -/
theorem inverseCache_clock (p W : ℕ) (constant : SignedWord) (slope : List Bool)
    (hc:constant.magnitude.length ≤ W) (hs:slope.length ≤ W) :
    (SemiprimeD1JetWordModeScalarBits.inverseCache p constant slope).clock ≤ inverseBudget p W := by
  let c:=SemiprimeD1RecoveryStripBits.signed p constant
  let s:=SemiprimeD1RecoveryStripBits.signed p (positive slope)
  let inverse:=SemiprimeD1OddInverseBits.inverse p c.bits
  let negative:=SemiprimeD1OddInverseBits.negativeOne p
  let opposite:=SemiprimeD1JetScalarBits.mul p negative.bits s.bits
  let ratio:=SemiprimeD1JetScalarBits.mul p opposite.bits inverse.bits
  let out:=geometric p ratio.bits inverse.bits p
  have hcc:c.clock ≤ 12*p*(p+W+2)+10*p+20:=
    (SemiprimeD1RecoveryStripBits.signed_clock p constant).trans (by gcongr)
  have hsc:s.clock ≤ 12*p*(p+W+2)+10*p+20:=
    (SemiprimeD1RecoveryStripBits.signed_clock p (positive slope)).trans (by gcongr;exact hs)
  have hsb:s.bits.length ≤ p:=(SemiprimeD1RecoveryStripBits.signed_good p (positive slope)).1
  have hic:inverse.clock ≤ 400*(p+1)^3:=SemiprimeD1OddInverseBounds.inverse_clock p c.bits
  have hib:inverse.bits.length ≤ p:=(SemiprimeD1OddInverseBits.inverse_good p c.bits).1
  have hnb:negative.bits.length ≤ p:=by simp only [negative,SemiprimeD1OddInverseBits.negativeOne,List.length_replicate,le_refl]
  have hoc:opposite.clock ≤ 50*(p+1)^2:=SemiprimeD1OddInverseBounds.mul_bounded p negative.bits s.bits hnb hsb
  have hob:opposite.bits.length ≤ p:=SemiprimeD1JetScalarBits.mul_length _ _ _
  have hrc:ratio.clock ≤ 50*(p+1)^2:=SemiprimeD1OddInverseBounds.mul_bounded p opposite.bits inverse.bits hob hib
  have hrb:ratio.bits.length ≤ p:=SemiprimeD1JetScalarBits.mul_length _ _ _
  have hgc:out.clock ≤ p*SemiprimeD1JetModeBitsBounds.geometricStage p+1:=
    SemiprimeD1JetModeBitsBounds.geometric_clock p ratio.bits inverse.bits p hrb hib
  have hnc:negative.clock=p+2:=rfl
  change c.clock+s.clock+inverse.clock+negative.clock+opposite.clock+ratio.clock+out.clock+15 ≤ _
  unfold inverseBudget
  omega

/-- Actual step-width bound derived from the acquired positive content. -/
theorem step_width (i : ℕ) (content : List Bool) (hc:0<bitValue content) :
    (SemiprimeD1JetWordModeScalarBits.step i content).bits.length ≤ i+2 := by
  have hq:=(divideBits_widths (xs:=(SemiprimeD1NormalizedLinearBits.alpha (i+1)).bits) hc).2
  rw [SemiprimeD1NormalizedLinearBits.alpha_length] at hq
  dsimp only [SemiprimeD1JetWordModeScalarBits.step]
  split
  · omega
  · simp only [List.length_cons,List.length_nil];omega

/-- Physical division and zero-clamp step budget. -/
def stepBudget (i W : ℕ) : ℕ :=
  6*(i+1)+3+(i+2)*(16*W+20)+7*W+4+3*(i+2)+1+5

/-- Step work is polynomial in actual content width and original level. -/
theorem step_clock (i W : ℕ) (content : List Bool) (hc:0<bitValue content)
    (hw:content.length ≤ W) :
    (SemiprimeD1JetWordModeScalarBits.step i content).clock ≤ stepBudget i W := by
  have hq:=(divideBits_widths (xs:=(SemiprimeD1NormalizedLinearBits.alpha (i+1)).bits) hc).2
  rw [SemiprimeD1NormalizedLinearBits.alpha_length] at hq
  have hd:=divideBits_cost (SemiprimeD1NormalizedLinearBits.alpha (i+1)).bits content
  rw [SemiprimeD1NormalizedLinearBits.alpha_length] at hd
  have hdb:(divideBits (SemiprimeD1NormalizedLinearBits.alpha (i+1)).bits content).clock ≤ 
      (i+2)*(16*W+20)+7*W+4:=hd.trans (by gcongr)
  have ht:=nonzeroBits_cost (divideBits (SemiprimeD1NormalizedLinearBits.alpha (i+1)).bits content).quotient
  rw [hq] at ht
  change (SemiprimeD1NormalizedLinearBits.alpha (i+1)).clock+
    (divideBits (SemiprimeD1NormalizedLinearBits.alpha (i+1)).bits content).clock+
    (nonzeroBits (divideBits (SemiprimeD1NormalizedLinearBits.alpha (i+1)).bits content).quotient).clock+5 ≤ _
  rw [SemiprimeD1NormalizedLinearBits.alpha_clock]
  unfold stepBudget
  omega

/-- Original scalar-input constructor budget, including both actual digit stages. -/
def budget (p a i : ℕ) : ℕ :=
  2*(4*(a+1)+1)+SemiprimeD1NormalizedLinearBits.budget (a+1) (a+1)+
    inverseBudget p (a+2)+stepBudget i (2*a+4)+8

/-- Actual original factors derive content positivity and all source widths. -/
theorem acquire_factor_bounds (p a i : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a)) :
    let f:=(SemiprimeD1JetWordModeScalarBits.acquireOriginal p a i t x y₀).factor
    0<bitValue f.content ∧f.content.length ≤ 2*a+4 ∧
      f.constant.magnitude.length ≤ a+2 ∧f.slope.length ≤ a+2 := by
  have hw:=SemiprimeD1NormalizedLinearBits.acquire_width (a+1) (a+1)
    (SemiprimeEncodedRowSelection.digits (a+1) t.val).bits
    (SemiprimeEncodedRowSelection.digits (a+1) (displacement a x y₀).val).bits
    (SemiprimeEncodedRowSelection.digits_length _ _).le
    (SemiprimeEncodedRowSelection.digits_length _ _).le
  have hc:=SemiprimeD1NormalizedLinearBits.acquire_content (a+1)
    (SemiprimeEncodedRowSelection.digits (a+1) t.val).bits
    (SemiprimeEncodedRowSelection.digits (a+1) (displacement a x y₀).val).bits
  dsimp only [SemiprimeD1JetWordModeScalarBits.acquireOriginal]
  change 0<bitValue (SemiprimeD1NormalizedLinearBits.acquire _ _ _).content ∧_
  refine ⟨by rw [hc];positivity,?_⟩
  rcases hw with ⟨h1,h2,h3⟩
  exact ⟨by omega,by omega,by omega⟩

/-- Complete scalar acquisition report from original input dimensions only. -/
theorem acquire_clock (p a i : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a)) :
    (SemiprimeD1JetWordModeScalarBits.acquireOriginal p a i t x y₀).clock ≤ budget p a i := by
  let j:=SemiprimeEncodedRowSelection.digits (a+1) t.val
  let d:=SemiprimeEncodedRowSelection.digits (a+1) (displacement a x y₀).val
  let f:=SemiprimeD1NormalizedLinearBits.acquire (a+1) j.bits d.bits
  have hf:=acquire_factor_bounds p a i t x y₀
  have hfc:f.clock ≤ SemiprimeD1NormalizedLinearBits.budget (a+1) (a+1):=
    SemiprimeD1NormalizedLinearBits.acquire_clock (a+1) (a+1) j.bits d.bits
      (SemiprimeEncodedRowSelection.digits_length _ _).le
      (SemiprimeEncodedRowSelection.digits_length _ _).le
  have hic:=inverseCache_clock p (a+2) f.constant f.slope hf.2.2.1 hf.2.2.2
  have hsc:=step_clock i (2*a+4) f.content hf.1 hf.2.1
  have hj:j.work=4*(a+1)+1:=SemiprimeEncodedRowSelection.digits_work _ _
  have hd:d.work=4*(a+1)+1:=SemiprimeEncodedRowSelection.digits_work _ _
  change j.work+d.work+f.clock+
    (SemiprimeD1JetWordModeScalarBits.inverseCache p f.constant f.slope).clock+
    (SemiprimeD1JetWordModeScalarBits.step i f.content).clock+8 ≤ _
  unfold budget
  omega

/-- Original acquired cache and step widths follow the actually acquired factor. -/
theorem acquire_width (p a i : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a)) :
    (SemiprimeD1JetWordModeScalarBits.acquireOriginal p a i t x y₀).cache.words.length=p ∧
    (∀w∈(SemiprimeD1JetWordModeScalarBits.acquireOriginal p a i t x y₀).cache.words,w.length ≤ p) ∧
    (SemiprimeD1JetWordModeScalarBits.acquireOriginal p a i t x y₀).step.length ≤ i+2 := by
  have hf:=acquire_factor_bounds p a i t x y₀
  exact ⟨SemiprimeD1JetWordModeScalarBits.inverseCache_length _ _ _,
    SemiprimeD1JetWordModeScalarBits.inverseCache_bounded _ _ _,step_width _ _ hf.1⟩
end RiemannGaussian.SemiprimeD1JetWordModeScalarBounds
