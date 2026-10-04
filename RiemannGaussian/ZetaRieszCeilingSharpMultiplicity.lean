/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingAllHeightMultiplicity
import RiemannGaussian.GaussianHalfLaplaceMoments

/-!
# A sharper all-height payment of the unchanged ceiling

The exact nonnegative moment recurrence improves the normalized Gaussian
source at damping 2701/1000. This proves actual zeros are simple in
`1-Re(rho)<=min(1/20000,6/(log(abs(Im rho)+2)+60000))`.
The fixed plateau extends from 50000 to 60000; beyond it the preceding
all-height width improves by at least 10/9.

The SAME joinedPhysical carrier therefore has its 42/25 ceiling under the
original exposure hypotheses in this larger paid layer. The entire original
fixed-strip ceiling remains OPEN. No carrier, factorial order, phase,
count, diagonal, allocation or physical mask is changed. The earlier
all-family positive-budget no-go remains valid.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Complex Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingSharpMultiplicity
open ZetaGaussianScaledBandBudget (width shift gaussianScale)
open ZetaGaussianExpandedScale GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)

/-- Nonnegativity of the SIXTEENTH actual half-Gaussian moment, joined
with the exact recurrence, gives a sharper rational transform enclosure.
The alternating recurrence coefficients are kept together throughout. -/
theorem normalized_unit_source_lower :
    (59/125 : ℝ) <= GaussianFermiLaplaceOrder.halfGaussian 1 (2701/2000) := by
  have hpos : (0 : ℝ) <= GaussianHalfLaplaceMoments.moment 16 (2701/2000) := by
    unfold GaussianHalfLaplaceMoments.moment
    apply integral_nonneg
    intro t
    unfold GaussianHalfLaplaceMoments.atom GaussianFermiZeroPair.window
    positivity
  have h0 := GaussianHalfLaplaceMoments.moment_zero (2701/2000)
  have h1 := GaussianHalfLaplaceMoments.moment_one (2701/2000)
  have h2 := GaussianHalfLaplaceMoments.moment_recurrence 0 (2701/2000)
  have h3 := GaussianHalfLaplaceMoments.moment_recurrence 1 (2701/2000)
  have h4 := GaussianHalfLaplaceMoments.moment_recurrence 2 (2701/2000)
  have h5 := GaussianHalfLaplaceMoments.moment_recurrence 3 (2701/2000)
  have h6 := GaussianHalfLaplaceMoments.moment_recurrence 4 (2701/2000)
  have h7 := GaussianHalfLaplaceMoments.moment_recurrence 5 (2701/2000)
  have h8 := GaussianHalfLaplaceMoments.moment_recurrence 6 (2701/2000)
  have h9 := GaussianHalfLaplaceMoments.moment_recurrence 7 (2701/2000)
  have h10 := GaussianHalfLaplaceMoments.moment_recurrence 8 (2701/2000)
  have h11 := GaussianHalfLaplaceMoments.moment_recurrence 9 (2701/2000)
  have h12 := GaussianHalfLaplaceMoments.moment_recurrence 10 (2701/2000)
  have h13 := GaussianHalfLaplaceMoments.moment_recurrence 11 (2701/2000)
  have h14 := GaussianHalfLaplaceMoments.moment_recurrence 12 (2701/2000)
  have h15 := GaussianHalfLaplaceMoments.moment_recurrence 13 (2701/2000)
  have h16 := GaussianHalfLaplaceMoments.moment_recurrence 14 (2701/2000)
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  linarith only [hpos, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

/-- Exact scale transport of the moment enclosure to the original
normalized source. No quadrature enters the proof. -/
theorem normalized_source_lower :
    (59/250 : ℝ) <= halfGaussian 4 (2701/1000) := by
  have hs := halfGaussian_scale (r := 2) (by norm_num) 1 (2701/2000)
  norm_num at hs
  linarith only [hs, normalized_unit_source_lower]

/-- The concrete dilation used above the already-paid plateau. -/
def adaptiveDilation (L : ℝ) : ℝ := (L+60000)/1000000

/-- The corresponding selected double-zero depth. -/
def adaptiveDepth (L : ℝ) : ℝ := 6/(L+60000)

/-- An explicit simplicity layer at every height, with no unevaluated
threshold or upper-height restriction. This is not an all-zero-free width. -/
def simplicityWidth (t : ℝ) : ℝ := min (1/20000) (adaptiveDepth (scale t))

theorem adaptiveDilation_lower {L : ℝ} (hL : 50000 <= L) :
    9/100 <= adaptiveDilation L := by
  unfold adaptiveDilation
  linarith

/-- The entire height-dependent depth has the same normalized damping
as the exact moment enclosure. -/
theorem adaptiveDepth_eq {L : ℝ} (hL : 50000 <= L) :
    adaptiveDepth L = (27/10)*width (adaptiveDilation L) := by
  have hne : L+60000 ≠ 0 := by linarith
  unfold adaptiveDepth adaptiveDilation width GaussianStripProfile.width
  field_simp
  ring

/-- Exact homogeneity, not an asymptotic approximation, reuses the
existing rational Gaussian lower enclosure at every allowed dilation. -/
theorem physical_source_lower {q : ℝ} (hq : 9/100 <= q) :
    (106200)*q <= halfGaussian (gaussianScale q) (width q*(2701/1000)) := by
  have hw := (ZetaGaussianExpandedScale.width_bounds hq).1
  have hq0 : 0 < q := by linarith
  have hs := halfGaussian_scale hw 4 (2701/1000)
  have hB : 4*width q^2 = gaussianScale q := by
    unfold width gaussianScale GaussianStripProfile.gaussianScale
    ring
  rw [hB, mul_comm (2701/1000)] at hs
  have he : width q*((106200)*q) = 59/250 := by
    unfold width GaussianStripProfile.width
    field_simp
    ring
  apply (mul_le_mul_iff_right₀ hw).mp
  rw [he, hs]
  exact normalized_source_lower

/-- A genuine lower bound for the complete multiplicity-weighted source.
The cotangent correction is paid and the nonnegative Poisson reserve is
retained. No simplicity or exposure assumption enters this theorem. -/
theorem selected_multiple_source_lower {a₁ q : ℝ} (ha₁ : 79/250 <= a₁)
    (hq : 9/100 <= q) (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= (27/10)*width q)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    67000*q-4 <= a₁ * ((analyticZetaZeroMultiplicity rho : ℝ) *
      (halfGaussian (gaussianScale q) (1+shift q-rho.1.re) -
        Real.pi^2*(1+shift q-rho.1.re)/(8*halfWidth 9 (shift q)^2)) +
      factor 9 (gaussianScale q) (shift q) *
        ((analyticZetaZeroMultiplicity rho : ℝ)/(1+shift q+
          halfWidth 9 (shift q)-rho.1.re))) := by
  have hq0 : 0 < q := by linarith
  have hx := (ZetaGaussianExpandedScale.shift_bounds hq).1
  have hη := (ZetaGaussianExpandedScale.geometry hq).1
  have hB := (ZetaGaussianExpandedScale.gaussianScale_bounds hq).1
  have hd : 0 < 1+shift q-rho.1.re := by linarith [rho.re_lt_one]
  have hshift : shift q = width q/1000 := by
    unfold shift width GaussianStripProfile.shift
    ring
  have hdu : 1+shift q-rho.1.re <= width q*(2701/1000) := by
    rw [hshift]
    nlinarith only [hnear]
  have hG := (physical_source_lower hq).trans (halfGaussian_antitone hB hdu)
  have hpi : Real.pi^2 <= 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hcot : Real.pi^2*(1+shift q-rho.1.re)/
      (8*halfWidth 9 (shift q)^2) <= 6 := by
    calc
      _ <= 16*((1/40500)*(2701/1000))/(8*(1/200 : ℝ)^2) := by
        gcongr
        · exact hdu.trans (mul_le_mul_of_nonneg_right
            (ZetaGaussianExpandedScale.width_bounds hq).2 (by norm_num))
      _ <= _ := by norm_num
  have hb : (106200)*q-6 <=
      halfGaussian (gaussianScale q) (1+shift q-rho.1.re) -
        Real.pi^2*(1+shift q-rho.1.re)/(8*halfWidth 9 (shift q)^2) := by
    linarith only [hG, hcot]
  have hmR : (2 : ℝ) <= analyticZetaZeroMultiplicity rho := by exact_mod_cast hm
  have hweighted := mul_le_mul hmR hb
    (by linarith : (0 : ℝ) <= (106200)*q-6) (by linarith)
  have hr : 0 <= factor 9 (gaussianScale q) (shift q) *
      ((analyticZetaZeroMultiplicity rho : ℝ)/(1+shift q+
        halfWidth 9 (shift q)-rho.1.re)) := by
    have hden : 0 < 1+shift q+halfWidth 9 (shift q)-rho.1.re := by linarith
    unfold factor
    positivity
  have ht : 2*((106200)*q-6) <= (analyticZetaZeroMultiplicity rho : ℝ) *
      (halfGaussian (gaussianScale q) (1+shift q-rho.1.re) -
        Real.pi^2*(1+shift q-rho.1.re)/(8*halfWidth 9 (shift q)^2)) +
      factor 9 (gaussianScale q) (shift q) *
        ((analyticZetaZeroMultiplicity rho : ℝ)/(1+shift q+
          halfWidth 9 (shift q)-rho.1.re)) := by
    linarith only [hweighted, hr]
  have hp := mul_le_mul ha₁ ht (by linarith : (0 : ℝ) <= 2*((106200)*q-6))
    (by linarith)
  linarith

/-- A global logarithmic tangent with a larger reference height pays
the log-log cost without consuming the new source slope. -/
theorem log_height_tangent {L : ℝ} (hL : 0 < L) :
    Real.log L <= L/200000+12 := by
  have href : Real.log (200000 : ℝ) <= 13 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 200000)).mpr
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) <= 27/10)
      (show (27/10 : ℝ) <= Real.exp 1 by linarith [Real.exp_one_gt_d9]) 13
    rw [<-Real.exp_nat_mul] at hp
    norm_num at hp
    linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hL (by norm_num : (0 : ℝ) < 200000))
  rw [Real.log_div hL.ne' (by norm_num : (200000 : ℝ) ≠ 0)] at h
  linarith

/-- A uniform rational surplus in Gaussian detector units, proved for
EVERY height in the unbounded adaptive range. It is not a Riesz credit. -/
theorem complete_cost_margin {L : ℝ} (hL : 50000 <= L) :
    36922*adaptiveDilation L+L/35+57*Real.log L+840+236431/700 <=
      67000*adaptiveDilation L-4 := by
  have hl := log_height_tangent (by linarith : 0 < L)
  unfold adaptiveDilation
  linarith

/-- The COMPLETE old arithmetic budget lies strictly below the new
double-zero source at every logarithmic height at least 50000. -/
theorem complete_cost_lt_source {L : ℝ} (hL : 50000 <= L) :
    36922*adaptiveDilation L+L/35+57*Real.log L+840 <
      67000*adaptiveDilation L-4 := by
  linarith only [complete_cost_margin hL]

/-- The concrete adaptive Gaussian discharges the unchanged complete
arithmetic inequality for any eligible phase family. -/
theorem family_no_multiple {a ω : ℕ -> ℝ} (ha : ∀ n, 0 <= a n) (hs : Summable a)
    (hp : ∀ t, 0 <= zetaPhaseKernel a ω t) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 -> 1 <= ω n)
    (hlog : Summable (fun n => tail a n*Real.log (ω n)))
    (ha0 : a 0 <= 37/200) (ha1 : 79/250 <= a 1)
    (hW : mass a <= 61/100) (hF : frequencyCost a ω <= 1/4)
    (rho : NontrivialZetaZero) (ht : 1000000 <= |rho.1.im|)
    (hL : 50000 <= scale rho.1.im)
    (hnear : 1-rho.1.re <= adaptiveDepth (scale rho.1.im))
    (hm : 2 <= analyticZetaZeroMultiplicity rho) : False := by
  have hq := adaptiveDilation_lower hL
  obtain ⟨hx, hxu⟩ := ZetaGaussianExpandedScale.shift_bounds hq
  have hx' : shift (adaptiveDilation (scale rho.1.im)) <= delta 9/4 := hxu.trans
    (by norm_num [delta, DerivativePowerExponents.alpha])
  have hnear' : 1-rho.1.re <= (27/10)*width (adaptiveDilation (scale rho.1.im)) := by
    simpa only [adaptiveDepth_eq hL] using hnear
  have hline : DirichletPowerParameters.line 9 < rho.1.re := by
    have hw := (ZetaGaussianExpandedScale.width_bounds hq).2
    have hd : (27/10 : ℝ)*(1/40500) < delta 9 := by
      norm_num [delta, DerivativePowerExponents.alpha]
    rw [delta_eq_one_sub_line] at hd
    linarith
  have h := gaussian_source_le_budget ha hs hp hω0 hω1 hω hlog 9 (by norm_num)
    (ZetaGaussianExpandedScale.gaussianScale_bounds hq).1 hx hx' rho (by linarith)
    (ZetaGaussianBandBudget.scale_lower ht) hline
  have hb := ZetaGaussianExpandedCost.budget_le (ha 0) ha0 (tsum_nonneg (tail_nonneg ha))
    hW hF hq ht
  have hl := selected_multiple_source_lower ha1 hq rho hnear' hm
  have hc := complete_cost_lt_source hL
  linarith only [h, hb, hl, hc]

/-- The exact existing contact family supplies every arithmetic premise;
there is no new prime-cancellation or prime-density assumption. -/
theorem adaptive_simple (rho : NontrivialZetaZero) (ht : 1000000 <= |rho.1.im|)
    (hL : 50000 <= scale rho.1.im)
    (hnear : 1-rho.1.re <= adaptiveDepth (scale rho.1.im)) :
    analyticZetaZeroMultiplicity rho = 1 := by
  have h0 : phaseContactExactFamily 0 = phaseContactExactCoefficients 0 := by
    simpa [phaseContactExactFamily, phaseContactFrequency] using
      phaseContactFrequencyFamily_apply phaseContactExactCoefficients 0
  have h1 : phaseContactExactFamily 1 = phaseContactExactCoefficients 1 := by
    simpa [phaseContactExactFamily, phaseContactFrequency] using
      phaseContactFrequencyFamily_apply phaseContactExactCoefficients 1
  have hm : ¬2 <= analyticZetaZeroMultiplicity rho := by
    intro hm
    exact family_no_multiple phaseContactExactFamily_nonneg ZetaExactPhaseAngularExclusion.exact_summable
      phaseContactExactFamily_kernel_nonneg (by norm_num) (by norm_num)
      (fun n hn => by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
      ZetaExactPhaseAngularExclusion.exact_log_summable
      (by rw [h0]; exact GaussianFermiProfileSurplus.exact_constant_upper)
      (by rw [h1]; exact GaussianFermiProfileSurplus.exact_first_lower)
      ZetaExactPhaseAngularExclusion.mass_bounds.2 ZetaGaussianBandExclusion.exact_frequency_cost
      rho ht hL hnear hm
  have hp := analyticZetaZeroMultiplicity_positive rho
  omega

/-- Every actual ordinate has a positive explicit simplicity width. -/
theorem simplicityWidth_pos (t : ℝ) : 0 < simplicityWidth t := by
  have hL : 0 < scale t := Real.log_pos (by
    unfold ZetaNearOneLogProfile.height
    linarith [abs_nonneg t])
  unfold simplicityWidth adaptiveDepth
  exact lt_min (by norm_num) (by positivity)

/-- The sharper moving curve joins the fixed candidate plateau at
logarithmic height 60000, extending the preceding 50000 plateau. -/
theorem simplicityWidth_eq_adaptive {t : ℝ} (hL : 60000 <= scale t) :
    simplicityWidth t = adaptiveDepth (scale t) := by
  unfold simplicityWidth
  apply min_eq_right
  unfold adaptiveDepth
  apply (div_le_iff₀ (by linarith : 0 < scale t+60000)).mpr
  linarith

/-- The entire original candidate width is now paid through logarithmic
height 60000, with no gap at the old plateau endpoint. -/
theorem simplicityWidth_eq_fixed {t : ℝ} (hL : scale t <= 60000) :
    simplicityWidth t = 1/20000 := by
  have hl : 0 < scale t := Real.log_pos (by
    unfold ZetaNearOneLogProfile.height
    linarith [abs_nonneg t])
  unfold simplicityWidth
  apply min_eq_left
  unfold adaptiveDepth
  apply (le_div_iff₀ (by positivity : 0 < scale t+60000)).mpr
  linarith

/-- At every height beyond the new plateau, the preceding all-height
simplicity width increases by at least 10/9. -/
theorem old_width_improvement {t : ℝ} (hL : 60000 <= scale t) :
    (10/9)*ZetaRieszCeilingAllHeightMultiplicity.simplicityWidth t <= simplicityWidth t := by
  rw [simplicityWidth_eq_adaptive hL,
    ZetaRieszCeilingAllHeightMultiplicity.simplicityWidth_eq_adaptive (by linarith : 50000 <= scale t)]
  unfold adaptiveDepth ZetaRieszCeilingAllHeightMultiplicity.adaptiveDepth
  have he : (10/9 : ℝ)*(9/(2*(scale t+40000)))=5/(scale t+40000) := by
    have hne : scale t+40000 ≠ 0 := by linarith
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ (by linarith : 0 < scale t+40000)
    (by linarith : 0 < scale t+60000)).mpr
  linarith

/-- The preceding paid simplicity layer is preserved at EVERY ordinate.
No smaller region is substituted for the fixed-strip objective. -/
theorem old_width_le (t : ℝ) :
    ZetaRieszCeilingAllHeightMultiplicity.simplicityWidth t <= simplicityWidth t := by
  by_cases hL : scale t <= 60000
  · rw [simplicityWidth_eq_fixed hL]
    exact min_le_left _ _
  have hi := old_width_improvement (le_of_lt (lt_of_not_ge hL))
  have hp := ZetaRieszCeilingAllHeightMultiplicity.simplicityWidth_pos t
  linarith

/-- A proved simplicity layer at EVERY height, without exposure,
simplicity, a new arithmetic premise, or an upper-height ceiling. -/
theorem simple_of_boundary_layer (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= simplicityWidth rho.1.im) :
    analyticZetaZeroMultiplicity rho = 1 := by
  by_cases hL : scale rho.1.im <= 50000
  · exact ZetaRieszCeilingGaussianMultiplicity.simple_of_narrow_strip_up_to_log_height rho hL
      (hnear.trans (min_le_left _ _))
  have hLa : 50000 <= scale rho.1.im := le_of_lt (lt_of_not_ge hL)
  have ht : 1000000 <= |rho.1.im| := by
    by_contra! ht
    have hlog : Real.log (|rho.1.im|+2) <= 20 := by
      have h := Real.log_le_log (by positivity : 0 < |rho.1.im|+2)
        (show |rho.1.im|+2 <= (2 : ℝ)^20 by norm_num; linarith)
      rw [Real.log_pow] at h
      have htwo : Real.log 2 <= 1 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num at h
      linarith
    change 50000 <= Real.log (|rho.1.im|+2) at hLa
    linarith
  exact adaptive_simple rho ht hLa (hnear.trans (min_le_right _ _))

/-- An independent all-height horizontal restriction on every actual
multiple zero. Simple zeros are NOT excluded by this statement. -/
theorem multiple_zero_margin (rho : NontrivialZetaZero)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    simplicityWidth rho.1.im < 1-rho.1.re := by
  by_contra! hnear
  have hs := simple_of_boundary_layer rho hnear
  omega

/-- The SAME joined physical carrier has the required ceiling wherever
the new independent all-height simplicity payment applies. -/
theorem eventually_joinedPhysical_ceiling_in_boundary_layer (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho ->
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling)
    (hnear : 1-rho.1.re <= simplicityWidth rho.1.im) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re < 42/25 := by
  have hm := simple_of_boundary_layer rho hnear
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  simp only [hm, Nat.cast_one, one_pow, one_mul, Complex.add_re, Complex.neg_re,
    Complex.one_re, Complex.ofReal_re] at hs
  have hu : 1/2 <= 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hc := ZetaRieszEndgameSlack.retainedCost_upper hu hU
  exact hs.eventually (gt_mem_nhds (show -1+ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) <
    42/25 by linarith only [hc]))

/-- The exact remaining multiplicity obstruction in the ORIGINAL fixed
candidate strip. This is a restriction, not a bound on that remainder. -/
theorem unpaid_multiple_location (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    60000 < scale rho.1.im ∧
      6/(scale rho.1.im+60000) < 1-rho.1.re ∧
      1-rho.1.re <= 1/20000 := by
  have hL : 60000 < scale rho.1.im := by
    by_contra! hL
    have hs := simple_of_boundary_layer rho
      (by rw [simplicityWidth_eq_fixed hL]; exact hnear)
    omega
  have hmarg := multiple_zero_margin rho hm
  rw [simplicityWidth_eq_adaptive hL.le] at hmarg
  exact ⟨hL, hmarg, hnear⟩

end RiemannGaussian.ZetaRieszCeilingSharpMultiplicity
