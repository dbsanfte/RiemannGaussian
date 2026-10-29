/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetWordModeBits

/-! # Complete word-mode report bounds after the acquired base entry
The literal actual base report is retained, not replaced by an old clock. All
remaining source/Horner/step/power stages have explicit original-input bounds.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1JetWordModeBounds
open SemiprimeBitArithmetic SemiprimeD1JetAxes
open SemiprimeD1JetAffineCoefficient (JetRun)
open SemiprimeD1JetPolynomialBits SemiprimeD1JetPolynomialBitsBounds
open SemiprimeD1JetAffineCoefficientBounds SemiprimeD1RecoveryIntegerBits
open SemiprimeD1WireKernelOriginal
attribute [local irreducible] SemiprimeD1JetWordModeScalarBits.acquireOriginal
  SemiprimeD1JetWordKernelBits.acquireOriginal

/-- Structural actual base rank and width, requiring no semantic unit advice. -/
theorem base_good (ctx : Context) (z : JetRun) (a : ℕ)
    (t : Fin (size a)) (x y₀ : Fin (2^a)) :
    Good ctx (SemiprimeD1JetWordKernelBits.acquireOriginal ctx z a t x y₀).words := by
  unfold SemiprimeD1JetWordKernelBits.acquireOriginal SemiprimeD1JetWordKernelBits.entry
  exact mul_good _ _ _

/-- Every non-base original source and physical mode stage, with exact repetitions. -/
def budget (ctx : Context) (W a i b : ℕ) : ℕ :=
  SemiprimeD1JetWordModeScalarBounds.budget ctx.precision a i+
  ctx.precision*(3*W+3*ctx.rank+
    SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+addBudget ctx W+12)+ctx.rank+1+
  (12*ctx.precision*(ctx.precision+(i+2)+2)+13*ctx.precision+3*ctx.rank+27)+
  2*SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+
  b*(SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+3)+
  9*ctx.precision+3*ctx.rank+8+20

/-- Complete actual mode clock, retaining the entire actual acquired-base clock. -/
theorem acquireOriginal_clock (ctx : Context) (z : JetRun) (a i b W : ℕ)
    (t : Fin (size a)) (x y₀ : Fin (2^a))
    (hp:ctx.precision ≤ W) (hz:z.words.length ≤ ctx.rank) (hw:∀w∈z.words,w.length ≤ W) :
    (SemiprimeD1JetWordModeBits.acquireOriginal ctx z a i b t x y₀).clock ≤ 
      (SemiprimeD1JetWordKernelBits.acquireOriginal ctx z a t x y₀).clock+budget ctx W a i b := by
  let base:=SemiprimeD1JetWordKernelBits.acquireOriginal ctx z a t x y₀
  let source:=SemiprimeD1JetWordModeScalarBits.acquireOriginal ctx.precision a i t x y₀
  let inverse:=horner ctx z.words source.cache.words
  let tile:=SemiprimeD1JetWordSourceBits.constant ctx (positive source.step)
  let ratio:=SemiprimeD1JetRingBits.mul ctx tile.words inverse.words
  let raised:=power ctx ratio.words b
  let out:=SemiprimeD1JetRingBits.mul ctx base.words raised.words
  have hsc:source.clock ≤ SemiprimeD1JetWordModeScalarBounds.budget ctx.precision a i:=
    SemiprimeD1JetWordModeScalarBounds.acquire_clock _ _ _ _ _ _
  have hsw:=SemiprimeD1JetWordModeScalarBounds.acquire_width ctx.precision a i t x y₀
  have hh:=horner_clock ctx z.words source.cache.words W hp hz hw (fun w h=>(hsw.2.1 w h).trans hp)
  rw [show source.cache.words.length=ctx.precision from hsw.1] at hh
  have ht:tile.clock ≤ 12*ctx.precision*(ctx.precision+(i+2)+2)+13*ctx.precision+3*ctx.rank+27:=by
    have h:=SemiprimeD1JetWordSourceBits.constant_clock ctx (positive source.step)
    exact h.trans (by gcongr;exact hsw.2.2)
  have htg:Good ctx tile.words:=SemiprimeD1JetWordSourceBits.constant_good ctx _
  have hhg:Good ctx inverse.words:=horner_good _ _ _
  have hr:=SemiprimeD1JetRingBounds.mul_clock ctx tile.words inverse.words W htg.1.le hhg.1.le
    (fun w h=>(htg.2 w h).trans hp) (fun w h=>(hhg.2 w h).trans hp)
  have hrg:Good ctx ratio.words:=mul_good _ _ _
  have hpw:=power_clock ctx ratio.words b W hp hrg.1.le (fun w h=>(hrg.2 w h).trans hp)
  have hpg:Good ctx raised.words:=power_good _ _ _
  have hbg:Good ctx base.words:=base_good ctx z a t x y₀
  have ho:=SemiprimeD1JetRingBounds.mul_clock ctx base.words raised.words W hbg.1.le hpg.1.le
    (fun w h=>(hbg.2 w h).trans hp) (fun w h=>(hpg.2 w h).trans hp)
  change inverse.clock ≤ _ at hh
  change ratio.clock ≤ _ at hr
  change raised.clock ≤ _ at hpw
  change out.clock ≤ _ at ho
  change base.clock+source.clock+inverse.clock+tile.clock+ratio.clock+raised.clock+out.clock+20 ≤ base.clock+_
  unfold budget
  omega
end RiemannGaussian.SemiprimeD1JetWordModeBounds
