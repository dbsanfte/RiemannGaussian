/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetKernelBits
import RiemannGaussian.SemiprimeD1OddInverseBounds

/-! # Original-data widths and retained physical acquired-entry reports
Original native integer construction and digit-stage integer bit costs are
separate; all emitted physical scalar/vector arithmetic is bounded here.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1JetKernelBitsBounds
open SemiprimeD1JetAxes SemiprimeD1JetKernelBits SemiprimeD1JetPolynomialBits
open SemiprimeD1JetPolynomialBitsBounds SemiprimeD1JetAffineCoefficientBounds

/-- Original signed source words have intrinsic modular precision width. -/
theorem integer_length (p : ℕ) (z : ℤ) : (integer p z).bits.length ≤ p := by
  unfold integer
  split
  · exact SemiprimeD1JetScalarBits.mul_length _ _ _
  · exact magnitude_length _ _

/-- Fixed polynomial signed-digit acquisition budget, without a magnitude-fit premise. -/
def integerBudget (p : ℕ) : ℕ :=12*p*(2*p+2)+20*p+30

/-- Every actual signed acquisition stage and physical negation is retained. -/
theorem integer_clock (p : ℕ) (z : ℤ) : (integer p z).clock ≤ integerBudget p := by
  have hc:=magnitude_clock p z.natAbs
  have hw:=magnitude_length p z.natAbs
  have hm:=SemiprimeD1JetScalarBits.mul_clock p
    (SemiprimeD1OddInverseBits.negativeOne p).bits (magnitude p z.natAbs).bits
  simp only [SemiprimeD1OddInverseBits.negativeOne,List.length_replicate] at hm
  have hmul : 12*p*(p+(magnitude p z.natAbs).bits.length+2) ≤ 12*p*(2*p+2) :=
    Nat.mul_le_mul_left (12*p) (by omega)
  unfold integer integerBudget
  split
  · change (magnitude p z.natAbs).clock+(p+2)+
      (SemiprimeD1JetScalarBits.mul p (List.replicate p true) (magnitude p z.natAbs).bits).clock+5 ≤ _
    nlinarith
  · change (magnitude p z.natAbs).clock+3 ≤ _
    nlinarith

/-- Every source integer vector has derived physical rank and width. -/
theorem integerVector_good (ctx : Context) (z : ℤ) : Good ctx (integerVector ctx z).words :=
  ⟨scalar_shape _ _,scalar_bounded _ _ _ (integer_length _ _)⟩

/-- Dense source-integer acquisition budget. -/
def integerVectorBudget (ctx : Context) : ℕ :=
  integerBudget ctx.precision+3*ctx.precision+3*ctx.rank+7

/-- Actual integer-vector encoding and allocation have their retained original-data budget. -/
theorem integerVector_clock (ctx : Context) (z : ℤ) :
    (integerVector ctx z).clock ≤ integerVectorBudget ctx := by
  have hi:=integer_clock ctx.precision z
  have hw:=integer_length ctx.precision z
  have hs:=scalar_clock ctx (integer ctx.precision z).bits
  change (integer ctx.precision z).clock+(scalar ctx (integer ctx.precision z).bits).clock+3 ≤ _
  unfold integerVectorBudget
  omega

/-- Every physical affine-factor output has target rank and precision. -/
theorem linear_good (ctx : Context) (z : List (List Bool)) (l : SemiprimeD1WireKernelFactors.Linear) :
    Good ctx (linear ctx z l).words := add_good _ _ _

/-- Whole physical affine factor budget, polynomial in actual context/word dimensions. -/
def linearBudget (ctx : Context) (W : ℕ) : ℕ :=
  2*integerVectorBudget ctx+SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+
    addBudget ctx W+5

/-- Both original integer sources and every physical multiply/add stage are paid. -/
theorem linear_clock (ctx : Context) (z : List (List Bool)) (l : SemiprimeD1WireKernelFactors.Linear)
    (W : ℕ) (hp : ctx.precision ≤ W) (hz : z.length ≤ ctx.rank) (hw : ∀w∈z,w.length ≤ W) :
    (linear ctx z l).clock ≤ linearBudget ctx W := by
  have hc:=integerVector_clock ctx l.constant
  have hs:=integerVector_clock ctx l.slope
  have hcg:=integerVector_good ctx l.constant
  have hsg:=integerVector_good ctx l.slope
  have hm:=SemiprimeD1JetRingBounds.mul_clock ctx (integerVector ctx l.slope).words z W hsg.1.le hz
    (fun w h=>(hsg.2 w h).trans hp) hw
  have hmg:=mul_good ctx (integerVector ctx l.slope).words z
  have ha:=SemiprimeD1JetRingBounds.add_clock ctx (integerVector ctx l.constant).words
    (SemiprimeD1JetRingBits.mul ctx (integerVector ctx l.slope).words z).words W hcg.1.le hmg.1.le
    (fun w h=>(hcg.2 w h).trans hp) (fun w h=>(hmg.2 w h).trans hp)
  change (integerVector ctx l.constant).clock+(integerVector ctx l.slope).clock+
    (SemiprimeD1JetRingBits.mul ctx (integerVector ctx l.slope).words z).clock+
    (SemiprimeD1JetRingBits.add ctx (integerVector ctx l.constant).words
      (SemiprimeD1JetRingBits.mul ctx (integerVector ctx l.slope).words z).words).clock+5 ≤ _
  unfold linearBudget addBudget
  omega

/-- Literal acquired report sums are bounded by their actual number of source records. -/
theorem report_sum_le {A : Type*} (xs : List A) (f : A→SemiprimeD1JetAffineCoefficient.JetRun)
    (B : ℕ) (h : ∀x∈xs,(f x).clock ≤ B) :
    ((xs.map f).map (fun r=>r.clock)).sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh:=h x List.mem_cons_self
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Every actual acquired-factor wire entry has intrinsic target shape/width. -/
theorem entry_good (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (e : SemiprimeD1WireKernelEntry.Entry) : Good ctx (entry ctx z e).words := mul_good _ _ _

/-- Closed physical entry budget after the explicitly native original integer constructor. -/
def entryBudget (ctx : Context) (W power factors : ℕ) : ℕ :=
  integerBudget ctx.precision+400*(ctx.precision+1)^3+(3*ctx.precision+3*ctx.rank+4)+
    integerVectorBudget ctx+
    power*(SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+3)+
    (9*ctx.precision+3*ctx.rank+8)+
    factors*(linearBudget ctx W+SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+3)+
    (9*ctx.precision+3*ctx.rank+8)+
    2*SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+20

/-- Original source jet report and every actual encoding, inverse, factor/power stage are retained.
There is no intermediate-fit, denominator-inverse or callback-clock premise. -/
theorem entry_clock (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (e : SemiprimeD1WireKernelEntry.Entry) (W : ℕ)
    (hp : ctx.precision ≤ W) (hz : z.words.length ≤ ctx.rank) (hw : ∀w∈z.words,w.length ≤ W) :
    (entry ctx z e).clock ≤ z.clock+entryBudget ctx W e.power e.factors.length := by
  have hd:=integer_clock ctx.precision e.denominator
  have hi:=SemiprimeD1OddInverseBounds.inverse_clock ctx.precision (integer ctx.precision e.denominator).bits
  have hig:=SemiprimeD1OddInverseBits.inverse_good ctx.precision (integer ctx.precision e.denominator).bits
  let inverseBits:=(SemiprimeD1OddInverseBits.inverse ctx.precision (integer ctx.precision e.denominator).bits).bits
  have hs:=scalar_clock ctx inverseBits
  have hsg : Good ctx (scalar ctx inverseBits).words:=⟨scalar_shape _ _,scalar_bounded _ _ _ hig.1⟩
  have ht:=integerVector_clock ctx 2
  have htg:=integerVector_good ctx 2
  have he:=power_clock ctx (integerVector ctx 2).words e.power W hp htg.1.le
    (fun w h=>(htg.2 w h).trans hp)
  have heg:=power_good ctx (integerVector ctx 2).words e.power
  have hf:=product_clock ctx (e.factors.map (linear ctx z.words)) W hp (by
    intro r hr
    rcases List.mem_map.mp hr with ⟨l,_,rfl⟩
    exact ⟨(linear_good ctx z.words l).1.le,fun w h=>((linear_good ctx z.words l).2 w h).trans hp⟩)
  have hfs:=report_sum_le e.factors (linear ctx z.words) (linearBudget ctx W)
    (fun l _=>linear_clock ctx z.words l W hp hz hw)
  simp only [List.length_map] at hf
  have hfg:=product_good ctx (e.factors.map (linear ctx z.words))
  have hl:=SemiprimeD1JetRingBounds.mul_clock ctx (scalar ctx inverseBits).words
    (power ctx (integerVector ctx 2).words e.power).words W hsg.1.le heg.1.le
    (fun w h=>(hsg.2 w h).trans hp) (fun w h=>(heg.2 w h).trans hp)
  have hlg:=mul_good ctx (scalar ctx inverseBits).words (power ctx (integerVector ctx 2).words e.power).words
  have ho:=SemiprimeD1JetRingBounds.mul_clock ctx
    (SemiprimeD1JetRingBits.mul ctx (scalar ctx inverseBits).words
      (power ctx (integerVector ctx 2).words e.power).words).words
    (product ctx (e.factors.map (linear ctx z.words))).words W hlg.1.le hfg.1.le
    (fun w h=>(hlg.2 w h).trans hp) (fun w h=>(hfg.2 w h).trans hp)
  change z.clock+(integer ctx.precision e.denominator).clock+
    (SemiprimeD1OddInverseBits.inverse ctx.precision (integer ctx.precision e.denominator).bits).clock+
    (scalar ctx inverseBits).clock+(integerVector ctx 2).clock+
    (power ctx (integerVector ctx 2).words e.power).clock+
    (product ctx (e.factors.map (linear ctx z.words))).clock+
    (SemiprimeD1JetRingBits.mul ctx (scalar ctx inverseBits).words
      (power ctx (integerVector ctx 2).words e.power).words).clock+
    (SemiprimeD1JetRingBits.mul ctx
      (SemiprimeD1JetRingBits.mul ctx (scalar ctx inverseBits).words
        (power ctx (integerVector ctx 2).words e.power).words).words
      (product ctx (e.factors.map (linear ctx z.words))).words).clock+20 ≤ _
  unfold entryBudget
  nlinarith

/-- Actual remaining two-power is bounded by original grid size times its depth. -/
theorem excess_le (k j d : ℕ) (hj : j<2^k) :
    SemiprimeD1WireKernelFactors.excess k j d ≤ 2^k*k := by
  have hs : (∑q∈(Finset.range (2^k)).erase d,
      SemiprimeD1WireKernelFactors.factorOrder k j q) ≤ 
      ((Finset.range (2^k)).erase d).card*k := by
    calc
      _  ≤  ∑q∈(Finset.range (2^k)).erase d,k := by
        apply Finset.sum_le_sum
        intro q hq
        exact SemiprimeD1WireKernelFactors.factorOrder_le k j q hj
          (Finset.mem_range.mp (Finset.mem_of_mem_erase hq))
      _ = _ := by simp
  have hc : ((Finset.range (2^k)).erase d).card ≤ 2^k :=
    (Finset.card_erase_le).trans (by simp)
  exact (Nat.sub_le _ _).trans (hs.trans (Nat.mul_le_mul_right k hc))

/-- Physical entry budget increases only with actual power/factor counts. -/
theorem entryBudget_mono (ctx : Context) (W p₁ p₂ f₁ f₂ : ℕ) (hp : p₁ ≤ p₂) (hf : f₁ ≤ f₂) :
    entryBudget ctx W p₁ f₁ ≤ entryBudget ctx W p₂ f₂ := by
  unfold entryBudget
  gcongr

/-- Original grid entry's physical encoding/evaluation budget is polynomial in actual grid size.
The original native integer constructor/digit integer-bit cost is explicitly separate. -/
theorem acquireOriginal_clock (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (x y : Fin (2^a)) (W : ℕ)
    (hp : ctx.precision ≤ W) (hz : z.words.length ≤ ctx.rank) (hw : ∀w∈z.words,w.length ≤ W) :
    (SemiprimeD1JetKernelBits.acquireOriginal ctx z a t x y).clock ≤ 
      z.clock+entryBudget ctx W (2^(a+1)*(a+1)) (2^(a+1)) := by
  have h:=entry_clock ctx z (SemiprimeD1WireKernelOriginal.acquireOriginal a t x y) W hp hz hw
  apply h.trans
  apply Nat.add_le_add_left
  apply entryBudget_mono
  · exact excess_le (a+1) t.val (SemiprimeD1WireKernelOriginal.displacement a x y).val t.isLt
  · simpa only [SemiprimeD1WireKernelOriginal.acquireOriginal,SemiprimeD1WireKernelEntry.acquire,
      List.length_map] using SemiprimeD1WireKernelEntry.indices_length (a+1)
        (SemiprimeD1WireKernelOriginal.displacement a x y).val

end RiemannGaussian.SemiprimeD1JetKernelBitsBounds
