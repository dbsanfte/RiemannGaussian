/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetWordKernelBits

/-! # Retained cost of the actual original-word kernel consumer
Every bound below concerns the new executed word program, including its own
factor, denominator and dyadic-quotient acquisition. Literal agreement with the
old integer program is not used to transfer a clock. Native small dimensions,
digit/control primitives and whole memory simulation remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1JetWordKernelBounds
open SemiprimeBitArithmetic SemiprimeBitIndexClipping SemiprimeD1JetAxes
open SemiprimeD1JetWordKernelBits SemiprimeD1JetPolynomialBits
open SemiprimeD1JetPolynomialBitsBounds SemiprimeD1JetAffineCoefficientBounds
open SemiprimeD1JetAffineCoefficient (JetRun)
open SemiprimeD1RecoveryIntegerBits (positive)

/-- Physical sign/reduction budget at an actual acquired source width. -/
def signedBudget (p W : ℕ) : ℕ := 12*p*(p+W+2)+10*p+20

/-- Physical source reduction and copied dense constant allocation. -/
def sourceBudget (ctx : Context) (W : ℕ) : ℕ :=
  12*ctx.precision*(ctx.precision+W+2)+13*ctx.precision+3*ctx.rank+27

/-- Actual byte-source acquisition is monotone in its literal input width. -/
theorem source_clock (ctx : Context) (word : SignedWord) (W : ℕ)
    (hw : word.magnitude.length≤W) :
    (SemiprimeD1JetWordSourceBits.constant ctx word).clock ≤ sourceBudget ctx W := by
  apply (SemiprimeD1JetWordSourceBits.constant_clock ctx word).trans
  unfold sourceBudget
  gcongr

/-- Both byte sources and the physical multiply and addition are retained. -/
def linearBudget (ctx : Context) (W : ℕ) : ℕ :=
  2*sourceBudget ctx W+
    SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+
    addBudget ctx W+5

/-- An acquired affine factor has intrinsic target rank and precision. -/
theorem linear_good (ctx : Context) (z : List (List Bool))
    (f : SemiprimeD1NormalizedLinearBits.Run) : Good ctx (linear ctx z f).words :=
  add_good _ _ _

/-- Every actually supplied factor byte is paid, without an integer source. -/
theorem linear_clock (ctx : Context) (z : List (List Bool))
    (f : SemiprimeD1NormalizedLinearBits.Run) (W : ℕ)
    (hp : ctx.precision≤W) (hz : z.length≤ctx.rank) (hw : ∀w∈z,w.length≤W)
    (hc : f.constant.magnitude.length≤W) (hs : f.slope.length≤W) :
    (linear ctx z f).clock≤linearBudget ctx W := by
  have hcc:=source_clock ctx f.constant W hc
  have hsc:=source_clock ctx (positive f.slope) W hs
  have hcg:=SemiprimeD1JetWordSourceBits.constant_good ctx f.constant
  have hsg:=SemiprimeD1JetWordSourceBits.constant_good ctx (positive f.slope)
  have hm:=SemiprimeD1JetRingBounds.mul_clock ctx
    (SemiprimeD1JetWordSourceBits.constant ctx (positive f.slope)).words z W hsg.1.le hz
    (fun w h=>(hsg.2 w h).trans hp) hw
  have hmg:=mul_good ctx (SemiprimeD1JetWordSourceBits.constant ctx (positive f.slope)).words z
  have ha:=SemiprimeD1JetRingBounds.add_clock ctx
    (SemiprimeD1JetWordSourceBits.constant ctx f.constant).words
    (SemiprimeD1JetRingBits.mul ctx
      (SemiprimeD1JetWordSourceBits.constant ctx (positive f.slope)).words z).words W
    hcg.1.le hmg.1.le (fun w h=>(hcg.2 w h).trans hp) (fun w h=>(hmg.2 w h).trans hp)
  change (SemiprimeD1JetWordSourceBits.constant ctx f.constant).clock+
    (SemiprimeD1JetWordSourceBits.constant ctx (positive f.slope)).clock+
    (SemiprimeD1JetRingBits.mul ctx
      (SemiprimeD1JetWordSourceBits.constant ctx (positive f.slope)).words z).clock+
    (SemiprimeD1JetRingBits.add ctx (SemiprimeD1JetWordSourceBits.constant ctx f.constant).words
      (SemiprimeD1JetRingBits.mul ctx
        (SemiprimeD1JetWordSourceBits.constant ctx (positive f.slope)).words z).words).clock+5≤_
  unfold linearBudget addBudget
  omega

/-- Complete actual entry report after its own word factory, counted separately. -/
def entryBudget (ctx : Context) (W F : ℕ) : ℕ :=
  signedBudget ctx.precision W+400*(ctx.precision+1)^3+
    (3*ctx.precision+3*ctx.rank+4)+sourceBudget ctx W+
    F*(linearBudget ctx W+
      SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+3)+
    (9*ctx.precision+3*ctx.rank+8)+
    2*SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+20

/-- The actual entry's final physical multiplication gives its full shape/width. -/
theorem entry_good (ctx : Context) (z : JetRun) (e : SemiprimeD1KernelEntryBits.Run) :
    Good ctx (entry ctx z e).words := mul_good _ _ _

/-- New denominator reduction, inverse, power-factor bytes and every cached
factor producer are retained. No old report occurs on either side. -/
theorem entry_clock (ctx : Context) (z : JetRun) (e : SemiprimeD1KernelEntryBits.Run)
    (W : ℕ) (hp : ctx.precision≤W) (hz : z.words.length≤ctx.rank)
    (hw : ∀w∈z.words,w.length≤W) (hd : e.denominator.magnitude.length≤W)
    (he : e.powerFactor.length≤W)
    (hf : ∀f∈e.factors,f.constant.magnitude.length≤W ∧ f.slope.length≤W) :
    (entry ctx z e).clock≤z.clock+entryBudget ctx W e.factors.length := by
  have hden:=(SemiprimeD1RecoveryStripBits.signed_clock ctx.precision e.denominator).trans
    (show 12*ctx.precision*(ctx.precision+e.denominator.magnitude.length+2)+
      10*ctx.precision+20 ≤ signedBudget ctx.precision W by unfold signedBudget;gcongr)
  let denominator:=SemiprimeD1RecoveryStripBits.signed ctx.precision e.denominator
  let inverseBits:=(SemiprimeD1OddInverseBits.inverse ctx.precision denominator.bits).bits
  have hi:=SemiprimeD1OddInverseBounds.inverse_clock ctx.precision denominator.bits
  have hig:=SemiprimeD1OddInverseBits.inverse_good ctx.precision denominator.bits
  have hs:=scalar_clock ctx inverseBits
  have hsg : Good ctx (scalar ctx inverseBits).words:=
    ⟨scalar_shape _ _,scalar_bounded _ _ _ hig.1⟩
  have ht:=source_clock ctx (positive e.powerFactor) W he
  have htg:=SemiprimeD1JetWordSourceBits.constant_good ctx (positive e.powerFactor)
  have hprod:=product_clock ctx (e.factors.map (linear ctx z.words)) W hp (by
    intro r hr
    obtain ⟨f,_,rfl⟩:=List.mem_map.mp hr
    exact ⟨(linear_good ctx z.words f).1.le,
      fun w h=>((linear_good ctx z.words f).2 w h).trans hp⟩)
  have hsum:=SemiprimeD1JetKernelBitsBounds.report_sum_le e.factors (linear ctx z.words)
    (linearBudget ctx W) (fun f h=>linear_clock ctx z.words f W hp hz hw (hf f h).1 (hf f h).2)
  simp only [List.length_map] at hprod
  have hpg:=product_good ctx (e.factors.map (linear ctx z.words))
  have hl:=SemiprimeD1JetRingBounds.mul_clock ctx (scalar ctx inverseBits).words
    (SemiprimeD1JetWordSourceBits.constant ctx (positive e.powerFactor)).words W hsg.1.le htg.1.le
    (fun w h=>(hsg.2 w h).trans hp) (fun w h=>(htg.2 w h).trans hp)
  have hlg:=mul_good ctx (scalar ctx inverseBits).words
    (SemiprimeD1JetWordSourceBits.constant ctx (positive e.powerFactor)).words
  have ho:=SemiprimeD1JetRingBounds.mul_clock ctx
    (SemiprimeD1JetRingBits.mul ctx (scalar ctx inverseBits).words
      (SemiprimeD1JetWordSourceBits.constant ctx (positive e.powerFactor)).words).words
    (product ctx (e.factors.map (linear ctx z.words))).words W hlg.1.le hpg.1.le
    (fun w h=>(hlg.2 w h).trans hp) (fun w h=>(hpg.2 w h).trans hp)
  change z.clock+denominator.clock+
    (SemiprimeD1OddInverseBits.inverse ctx.precision denominator.bits).clock+
    (scalar ctx inverseBits).clock+
    (SemiprimeD1JetWordSourceBits.constant ctx (positive e.powerFactor)).clock+
    (product ctx (e.factors.map (linear ctx z.words))).clock+
    (SemiprimeD1JetRingBits.mul ctx (scalar ctx inverseBits).words
      (SemiprimeD1JetWordSourceBits.constant ctx (positive e.powerFactor)).words).clock+
    (SemiprimeD1JetRingBits.mul ctx
      (SemiprimeD1JetRingBits.mul ctx (scalar ctx inverseBits).words
        (SemiprimeD1JetWordSourceBits.constant ctx (positive e.powerFactor)).words).words
      (product ctx (e.factors.map (linear ctx z.words))).words).clock+20≤_
  unfold entryBudget
  nlinarith

/-- Actual factor-count monotonicity, with no change to source multiplicity. -/
theorem entryBudget_mono (ctx : Context) (W F G : ℕ) (h : F≤G) :
    entryBudget ctx W F≤entryBudget ctx W G := by
  unfold entryBudget
  gcongr

/-- A single original-dimension width dominates all acquired factor, denominator
and quotient words, even before precision reduction. -/
def originalWidth (a N : ℕ) : ℕ := 2*N*(2*a+5)+a+5

/-- Original input only: all physical source widths are internally derived. -/
theorem acquire_widths (a : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (x y : Fin (2^a)) :
    (SemiprimeD1KernelEntryBits.acquireOriginal a t x y).denominator.magnitude.length≤
        originalWidth a (SemiprimeD1WireKernelOriginal.size a) ∧
    (SemiprimeD1KernelEntryBits.acquireOriginal a t x y).powerFactor.length≤
        originalWidth a (SemiprimeD1WireKernelOriginal.size a) ∧
    ∀f∈(SemiprimeD1KernelEntryBits.acquireOriginal a t x y).factors,
      f.constant.magnitude.length≤originalWidth a (SemiprimeD1WireKernelOriginal.size a) ∧
      f.slope.length≤originalWidth a (SemiprimeD1WireKernelOriginal.size a) := by
  have hd:=SemiprimeD1KernelDenominatorBits.run_width a
  have he:=SemiprimeD1KernelEntryBounds.powerFactor_width a t x y
  have hf:=(SemiprimeD1KernelEntryBounds.acquire_factor_bounds a t x y).2
  constructor
  · change (SemiprimeD1KernelDenominatorBits.run a).word.magnitude.length≤_
    unfold originalWidth
    nlinarith
  constructor
  · unfold originalWidth SemiprimeD1KernelEntryBounds.contentWidth at *
    omega
  intro f h
  have hb:=hf f h
  unfold originalWidth
  constructor <;> nlinarith [Nat.zero_le (2*SemiprimeD1WireKernelOriginal.size a*(2*a+5))]

/-- Complete actual original-word factory and consumer budget. -/
def budget (ctx : Context) (W a : ℕ) : ℕ :=
  SemiprimeD1KernelEntryBounds.budget a (SemiprimeD1WireKernelOriginal.size a)+
    entryBudget ctx (W+originalWidth a (SemiprimeD1WireKernelOriginal.size a))
      (SemiprimeD1WireKernelOriginal.size a)+3

/-- Original indices alone acquire all source data, with a fixed polynomial in
the actual grid size and physical jet dimensions; the source jet is paid once. -/
theorem acquireOriginal_clock (ctx : Context) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (x y : Fin (2^a)) (W : ℕ)
    (hp : ctx.precision≤W) (hz : z.words.length≤ctx.rank) (hw : ∀w∈z.words,w.length≤W) :
    (acquireOriginal ctx z a t x y).clock≤z.clock+budget ctx W a := by
  let V:=W+originalWidth a (SemiprimeD1WireKernelOriginal.size a)
  have hWV:W≤V:=Nat.le_add_right _ _
  have hOV:originalWidth a (SemiprimeD1WireKernelOriginal.size a)≤V:=Nat.le_add_left _ _
  have hs:=acquire_widths a t x y
  have h:=entry_clock ctx z (SemiprimeD1KernelEntryBits.acquireOriginal a t x y) V
    (hp.trans hWV) hz (fun w h=>(hw w h).trans hWV) (hs.1.trans hOV) (hs.2.1.trans hOV)
    (fun f hf=>⟨((hs.2.2 f hf).1).trans hOV,((hs.2.2 f hf).2).trans hOV⟩)
  have hF:=(SemiprimeD1KernelEntryBounds.acquire_factor_bounds a t x y).1
  have hm:=entryBudget_mono ctx V _ (SemiprimeD1WireKernelOriginal.size a) hF
  have hc:=SemiprimeD1KernelEntryBounds.acquire_clock a t x y
  change (SemiprimeD1KernelEntryBits.acquireOriginal a t x y).clock+
    (entry ctx z (SemiprimeD1KernelEntryBits.acquireOriginal a t x y)).clock+3≤_
  unfold budget
  dsimp only [V] at h hm
  omega

end RiemannGaussian.SemiprimeD1JetWordKernelBounds
