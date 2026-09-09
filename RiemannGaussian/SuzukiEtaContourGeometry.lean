/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaExtendedLimit
import RiemannGaussian.SuzukiCarrierRealContour

/-!
# Actual eta-compatible contour sides across the dyadic boundary

The dyadic completion exceptions form a countable set on spectral height
one half. Coordinates avoiding both these exceptions and the complete
xi/carrier singular set exist in every open interval. This constructs
arbitrarily large real-bottom and displaced-bottom contours compatible
with the wider finite eta approximation, rather than assuming their sides
are available.
-/

open Complex Filter Metric Set Topology
namespace RiemannGaussian
noncomputable section

/-- The elementary dyadic exceptions in the original spectral coordinate. -/
def suzukiXiEtaCompletionExceptions : Set ℂ :=
  {z | pairedEtaFactor (suzukiArithmeticZetaArgument z) = 0}

/-- Every dyadic completion exception lies on spectral height one half. -/
theorem im_eq_half_of_mem_suzukiXiEtaCompletionExceptions {z : ℂ}
    (hz : z ∈ suzukiXiEtaCompletionExceptions) : z.im = 1 / 2 := by
  have he := pairedEtaFactor_eq_zero_implies_re_eq_one hz
  rw [suzukiArithmeticZetaArgument_re] at he
  linarith

/-- The completion exceptions are countable, as zeros of a genuine
nonzero entire function. No zeta zero location is assumed. -/
theorem countable_suzukiXiEtaCompletionExceptions : suzukiXiEtaCompletionExceptions.Countable := by
  let g : ℂ → ℂ := fun z => pairedEtaFactor (suzukiArithmeticZetaArgument z)
  have hF : Differentiable ℂ pairedEtaFactor := fun s => (hasDerivAt_pairedEtaFactor s).differentiableAt
  have hg : ∀ z, AnalyticAt ℂ g z := fun z =>
    (hF.analyticAt _).comp (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
  have hgne : g 0 ≠ 0 := pairedEtaFactor_ne_zero_of_re_lt_one (by
    rw [suzukiArithmeticZetaArgument_re]
    norm_num)
  have hco := (show AnalyticOnNhd ℂ g univ from fun z _ => hg z).preimage_zero_mem_codiscrete hgne
  have hdisc : IsDiscrete suzukiXiEtaCompletionExceptions := by
    have he : (g ⁻¹' ({0} : Set ℂ)ᶜ)ᶜ = suzukiXiEtaCompletionExceptions := by
      ext z
      simp [suzukiXiEtaCompletionExceptions, g]
    rw [← he]
    exact (mem_codiscrete'.mp hco).2
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc

/-- A vertical coordinate avoids the genuine carrier singularities and
the elementary completion exceptions along its entire line. -/
def SuzukiXiEtaVerticalAdmissible (v : ℝ) : Prop :=
  (∀ c ∈ suzukiXiCarrierSingularSet, c.re ≠ v) ∧
    ∀ c ∈ suzukiXiEtaCompletionExceptions, c.re ≠ v

/-- Every open interval contains an actual vertical coordinate usable
by the complete signed contour and by the finite eta representation. -/
theorem exists_suzukiXiEtaVerticalAdmissible {a b : ℝ} (hab : a < b) :
    ∃ v ∈ Ioo a b, SuzukiXiEtaVerticalAdmissible v := by
  let bad : Set ℝ := re '' suzukiXiCarrierSingularSet ∪ re '' suzukiXiEtaCompletionExceptions
  have hbad : bad.Countable := (countable_suzukiXiCarrierSingularSet.image _).union
    (countable_suzukiXiEtaCompletionExceptions.image _)
  obtain ⟨v, hv, hgood⟩ := (hbad.dense_compl ℝ).inter_open_nonempty
    (Ioo a b) isOpen_Ioo (nonempty_Ioo.mpr hab)
  exact ⟨v, hv, ⟨fun c hc he => hgood (Or.inl ⟨c, hc, he⟩),
    fun c hc he => hgood (Or.inr ⟨c, hc, he⟩)⟩⟩

/-- Every point above spectral height minus one half on an admissible
vertical line belongs to the true finite-eta convergence domain. This
includes the entire closed strip segment from zero to one half. -/
theorem mem_suzukiXiEtaExtendedCarrierDomain_vertical {v y : ℝ}
    (hv : SuzukiXiEtaVerticalAdmissible v) (hy : -1 / 2 < y) :
    (v : ℂ) + (y : ℂ) * I ∈ suzukiXiEtaExtendedCarrierDomain := by
  let z : ℂ := (v : ℂ) + (y : ℂ) * I
  have hF : pairedEtaFactor (suzukiArithmeticZetaArgument z) ≠ 0 :=
    fun he => hv.2 z he (by simp [z])
  refine ⟨⟨?_, ?_, hF⟩, fun he => hv.1 z (Or.inr he) (by simp [z])⟩
  · rw [suzukiArithmeticZetaArgument_re]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
      zero_mul, add_zero, zero_add]
    linarith
  · intro he
    apply hF
    rw [he]
    norm_num [pairedEtaFactor, Complex.cpow_neg_one]

/-- The eta convergence domain includes every nonexceptional point
strictly above spectral height minus one half and away from height one
half. Nonvanishing of the genuine carrier denominator is explicit. -/
theorem mem_suzukiXiEtaExtendedCarrierDomain_of_im_ne_half {z : ℂ}
    (hlo : -1 / 2 < z.im) (hhalf : z.im ≠ 1 / 2) (hE : suzukiXiEValue z ≠ 0) :
    z ∈ suzukiXiEtaExtendedCarrierDomain := by
  have hF : pairedEtaFactor (suzukiArithmeticZetaArgument z) ≠ 0 :=
    fun he => hhalf (im_eq_half_of_mem_suzukiXiEtaCompletionExceptions he)
  refine ⟨⟨?_, ?_, hF⟩, hE⟩
  · rw [suzukiArithmeticZetaArgument_re]
    linarith
  · intro he
    apply hF
    rw [he]
    norm_num [pairedEtaFactor, Complex.cpow_neg_one]

/-- Arbitrarily large real-bottom contours have eta-compatible vertical
sides. Real xi zeros on the horizontal bottom are still allowed and
must use the separate removable-boundary analysis. -/
theorem exists_suzukiXiEtaRealRectangleAdmissible {R : ℝ} (hR : 1 ≤ R) :
    ∃ l r u : ℝ, SuzukiXiCarrierRealRectangleAdmissible l r u ∧
      SuzukiXiEtaVerticalAdmissible l ∧ SuzukiXiEtaVerticalAdmissible r ∧
      (-R - 1 < l ∧ l < -R) ∧ (R < r ∧ r < R + 1) ∧ R < u ∧ u < R + 1 := by
  obtain ⟨l, hl, hlsafe⟩ := exists_suzukiXiEtaVerticalAdmissible (a := -R - 1) (b := -R) (by linarith)
  obtain ⟨r, hr, hrsafe⟩ := exists_suzukiXiEtaVerticalAdmissible (a := R) (b := R + 1) (by linarith)
  obtain ⟨u, hu, husafe⟩ := exists_suzukiXiCarrier_safe_coordinate (a := R) (b := R + 1) (by linarith)
  exact ⟨l, r, u, ⟨by linarith [hl.2, hr.1], by linarith [hu.1], fun c hc =>
    ⟨hlsafe.1 c hc, hrsafe.1 c hc, (husafe c hc).2⟩⟩, hlsafe, hrsafe, hl, hr, hu⟩

/-- Eta-compatible upper rectangles expand arbitrarily far while their
positive bottom can be chosen arbitrarily close to the real axis. All
contour sides avoid the full actual singular set. -/
theorem exists_suzukiXiEtaUpperRectangleAdmissible {R delta : ℝ}
    (hR : 1 ≤ R) (hdelta : 0 < delta) :
    ∃ l r b u : ℝ, SuzukiXiCarrierRectangleAdmissible l r b u ∧
      SuzukiXiEtaVerticalAdmissible l ∧ SuzukiXiEtaVerticalAdmissible r ∧
      (-R - 1 < l ∧ l < -R) ∧ (R < r ∧ r < R + 1) ∧
      (0 < b ∧ b < delta ∧ b < 1 / 2) ∧ (R < u ∧ u < R + 1) := by
  obtain ⟨l, r, u, hadm, hlv, hrv, hl, hr, hu⟩ := exists_suzukiXiEtaRealRectangleAdmissible hR
  obtain ⟨b, hb, hbsafe⟩ := exists_suzukiXiCarrier_safe_coordinate
    (a := 0) (b := min delta (1 / 2)) (lt_min hdelta (by norm_num))
  have hbdelta := hb.2.trans_le (min_le_left _ _)
  have hbhalf := hb.2.trans_le (min_le_right _ _)
  exact ⟨l, r, b, u, ⟨hadm.1, by linarith [hu.1], fun c hc =>
    ⟨hlv.1 c hc, hrv.1 c hc, (hbsafe c hc).2, (hadm.2.2 c hc).2.2⟩⟩,
    hlv, hrv, hl, hr, ⟨hb.1, hbdelta, hbhalf⟩, hu⟩

end
end RiemannGaussian
