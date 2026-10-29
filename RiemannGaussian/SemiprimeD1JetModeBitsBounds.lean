/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetModeBits
import RiemannGaussian.SemiprimeD1JetKernelBitsBounds

/-! # Derived widths and concrete clocks of finite acquired crossing modes -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1JetModeBitsBounds
open SemiprimeD1JetAxes SemiprimeD1JetModeBits SemiprimeD1JetKernelBits
open SemiprimeD1JetKernelBitsBounds SemiprimeD1JetPolynomialBits
open SemiprimeD1JetPolynomialBitsBounds SemiprimeD1JetAffineCoefficientBounds

/-- Every finite scalar-cache prefix has the target physical precision width. -/
theorem geometric_bounded (p : ℕ) (ratio current : List Bool) (n : ℕ) (hc : current.length ≤ p) :
    ∀w∈(geometric p ratio current n).words,w.length ≤ p := by
  induction n generalizing current with
  | zero => simp [geometric]
  | succ n ih =>
    intro w hw
    rcases List.mem_cons.mp hw with he|ht
    · subst w
      simpa only [SemiprimeSourceCompactBits.copy_bits] using hc
    · exact ih _ (SemiprimeD1JetScalarBits.mul_length _ _ _) w ht

/-- Actual per-coefficient physical acquisition budget. -/
def geometricStage (p : ℕ) : ℕ:=3*p+50*(p+1)^2+6

/-- Every scalar copy/product and each recursively acquired cache cell is paid. -/
theorem geometric_clock (p : ℕ) (ratio current : List Bool) (n : ℕ)
    (hr : ratio.length ≤ p) (hc : current.length ≤ p) :
    (geometric p ratio current n).clock ≤ n*geometricStage p+1 := by
  induction n generalizing current with
  | zero => simp [geometric]
  | succ n ih =>
    have ht:=ih (SemiprimeD1JetScalarBits.mul p ratio current).bits
      (SemiprimeD1JetScalarBits.mul_length p ratio current)
    have hm:=SemiprimeD1OddInverseBounds.mul_bounded p ratio current hr hc
    have hh:=SemiprimeSourceCompactBits.copy_clock current
    change (SemiprimeSourceCompactBits.copy current).clock+
      (SemiprimeD1JetScalarBits.mul p ratio current).clock+
      (geometric p ratio (SemiprimeD1JetScalarBits.mul p ratio current).bits n).clock+5 ≤ _
    unfold geometricStage at ht ⊢
    nlinarith

/-- All actual inverse-cache coefficient words have target precision width. -/
theorem inverseCache_bounded (p : ℕ) (constant slope : ℤ) :
    ∀w∈(inverseCache p constant slope).words,w.length ≤ p :=
  geometric_bounded _ _ _ _ (SemiprimeD1OddInverseBits.inverse_good _ _).1

/-- Closed finite cache acquisition budget, cubic in actual precision. -/
def inverseCacheBudget (p : ℕ) : ℕ :=
  2*integerBudget p+400*(p+1)^3+p+2+100*(p+1)^2+p*geometricStage p+16

/-- Original constants/slopes acquire their entire finite inverse cache physically. -/
theorem inverseCache_clock (p : ℕ) (constant slope : ℤ) :
    (inverseCache p constant slope).clock ≤ inverseCacheBudget p := by
  have hc:=integer_clock p constant
  have hs:=integer_clock p slope
  have hi:=SemiprimeD1OddInverseBounds.inverse_clock p (integer p constant).bits
  have hig:=SemiprimeD1OddInverseBits.inverse_good p (integer p constant).bits
  have hn : (SemiprimeD1OddInverseBits.negativeOne p).bits.length ≤ p := by
    simp [SemiprimeD1OddInverseBits.negativeOne]
  have ho:=SemiprimeD1OddInverseBounds.mul_bounded p (SemiprimeD1OddInverseBits.negativeOne p).bits
    (integer p slope).bits hn (integer_length p slope)
  have hr:=SemiprimeD1OddInverseBounds.mul_bounded p
    (SemiprimeD1JetScalarBits.mul p (SemiprimeD1OddInverseBits.negativeOne p).bits (integer p slope).bits).bits
    (SemiprimeD1OddInverseBits.inverse p (integer p constant).bits).bits
    (SemiprimeD1JetScalarBits.mul_length _ _ _) hig.1
  have hg:=geometric_clock p
    (SemiprimeD1JetScalarBits.mul p
      (SemiprimeD1JetScalarBits.mul p (SemiprimeD1OddInverseBits.negativeOne p).bits (integer p slope).bits).bits
      (SemiprimeD1OddInverseBits.inverse p (integer p constant).bits).bits).bits
    (SemiprimeD1OddInverseBits.inverse p (integer p constant).bits).bits p
    (SemiprimeD1JetScalarBits.mul_length _ _ _) hig.1
  change (integer p constant).clock+(integer p slope).clock+
    (SemiprimeD1OddInverseBits.inverse p (integer p constant).bits).clock+
    (SemiprimeD1OddInverseBits.negativeOne p).clock+
    (SemiprimeD1JetScalarBits.mul p (SemiprimeD1OddInverseBits.negativeOne p).bits (integer p slope).bits).clock+
    (SemiprimeD1JetScalarBits.mul p
      (SemiprimeD1JetScalarBits.mul p (SemiprimeD1OddInverseBits.negativeOne p).bits (integer p slope).bits).bits
      (SemiprimeD1OddInverseBits.inverse p (integer p constant).bits).bits).clock+
    (geometric p
      (SemiprimeD1JetScalarBits.mul p
        (SemiprimeD1JetScalarBits.mul p (SemiprimeD1OddInverseBits.negativeOne p).bits (integer p slope).bits).bits
        (SemiprimeD1OddInverseBits.inverse p (integer p constant).bits).bits).bits
      (SemiprimeD1OddInverseBits.inverse p (integer p constant).bits).bits p).clock+15 ≤ _
  simp only [SemiprimeD1OddInverseBits.negativeOne] at ho hr hg ⊢
  unfold inverseCacheBudget
  nlinarith

/-- Every physical crossing mode has intrinsic target rank and precision. -/
theorem mode_good (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (k center i j d b : ℕ) : Good ctx (mode ctx z k center i j d b).words := mul_good _ _ _

/-- Fixed polynomial physical mode budget after the native acquired-factor constructor. -/
def modeBudget (ctx : Context) (W power factors degree : ℕ) : ℕ :=
  entryBudget ctx W power factors+inverseCacheBudget ctx.precision+
    ctx.precision*(3*W+3*ctx.rank+
      SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+addBudget ctx W+12)+ctx.rank+1+
    integerVectorBudget ctx+2*SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+
    degree*(SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+3)+
    (9*ctx.precision+3*ctx.rank+8)+20

/-- All physical base/cache/Horner/tile/power reports are retained once from original data. -/
theorem mode_clock (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (k center i j d b W : ℕ) (hp : ctx.precision ≤ W)
    (hz : z.words.length ≤ ctx.rank) (hw : ∀w∈z.words,w.length ≤ W) :
    (mode ctx z k center i j d b).clock ≤ z.clock+
      modeBudget ctx W (SemiprimeD1WireKernelEntry.acquire k center j d).power
        (SemiprimeD1WireKernelEntry.acquire k center j d).factors.length b := by
  let e:=SemiprimeD1WireKernelEntry.acquire k center j d
  let l:=SemiprimeD1WireKernelFactors.normalizedFactor k j d
  let cache:=inverseCache ctx.precision l.constant l.slope
  let invJet:=horner ctx z.words cache.words
  let tile:=integerVector ctx (SemiprimeD1CrossingExpansion.step k i j d)
  let ratio:=SemiprimeD1JetRingBits.mul ctx tile.words invJet.words
  let raised:=power ctx ratio.words b
  have he:=entry_clock ctx z e W hp hz hw
  have hc:=inverseCache_clock ctx.precision l.constant l.slope
  have hcb:=inverseCache_bounded ctx.precision l.constant l.slope
  have hh:=horner_clock ctx z.words cache.words W hp hz hw (fun w h=>(hcb w h).trans hp)
  have hcl : cache.words.length=ctx.precision:=inverseCache_length _ _ _
  rw [hcl] at hh
  have ht:=integerVector_clock ctx (SemiprimeD1CrossingExpansion.step k i j d)
  have htg : Good ctx tile.words:=integerVector_good _ _
  have hhg : Good ctx invJet.words:=horner_good _ _ _
  have hr:=SemiprimeD1JetRingBounds.mul_clock ctx tile.words invJet.words W htg.1.le hhg.1.le
    (fun w h=>(htg.2 w h).trans hp) (fun w h=>(hhg.2 w h).trans hp)
  have hrg : Good ctx ratio.words:=mul_good _ _ _
  have hpw:=power_clock ctx ratio.words b W hp hrg.1.le (fun w h=>(hrg.2 w h).trans hp)
  have hpg : Good ctx raised.words:=power_good _ _ _
  have heg:=entry_good ctx z e
  have ho:=SemiprimeD1JetRingBounds.mul_clock ctx (entry ctx z e).words raised.words W heg.1.le hpg.1.le
    (fun w h=>(heg.2 w h).trans hp) (fun w h=>(hpg.2 w h).trans hp)
  change (entry ctx z e).clock+cache.clock+invJet.clock+tile.clock+ratio.clock+raised.clock+
    (SemiprimeD1JetRingBits.mul ctx (entry ctx z e).words raised.words).clock+20 ≤ _
  unfold modeBudget
  nlinarith

/-- The closed mode budget is monotone in actual acquired power/factor counts. -/
theorem modeBudget_mono (ctx : Context) (W p₁ p₂ f₁ f₂ b : ℕ) (hp : p₁ ≤ p₂) (hf : f₁ ≤ f₂) :
    modeBudget ctx W p₁ f₁ b ≤ modeBudget ctx W p₂ f₂ b := by
  unfold modeBudget
  have h:=entryBudget_mono ctx W p₁ p₂ f₁ f₂ hp hf
  omega

/-- Original grid mode's whole retained physical report is original-dimension polynomial.
Native integer constructors, digit-stage big-integer work and address compilation remain separate. -/
theorem acquireOriginal_clock (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a i b : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (x y₀ : Fin (2^a)) (W : ℕ)
    (hp : ctx.precision ≤ W) (hz : z.words.length ≤ ctx.rank) (hw : ∀w∈z.words,w.length ≤ W) :
    (SemiprimeD1JetModeBits.acquireOriginal ctx z a i b t x y₀).clock ≤ z.clock+
      modeBudget ctx W (2^(a+1)*(a+1)) (2^(a+1)) b := by
  have h:=mode_clock ctx z (a+1) (SemiprimeD1WireKernelOriginal.center a) i t.val
    (SemiprimeD1CrossingPaper.baseIndex a x y₀) b W hp hz hw
  apply h.trans
  apply Nat.add_le_add_left
  apply modeBudget_mono
  · exact excess_le (a+1) t.val (SemiprimeD1CrossingPaper.baseIndex a x y₀) t.isLt
  · simpa only [SemiprimeD1WireKernelEntry.acquire,List.length_map] using
      SemiprimeD1WireKernelEntry.indices_length (a+1) (SemiprimeD1CrossingPaper.baseIndex a x y₀)

end RiemannGaussian.SemiprimeD1JetModeBitsBounds
