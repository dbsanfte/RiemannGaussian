/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianExpandedRegion
import RiemannGaussian.ZetaGaussianMultiplicityDepth
import RiemannGaussian.ZetaRieszEndgameSlack

/-!
# A genuine multiplicity payment for the current ceiling

The existing complete Gaussian budget retains actual analytic multiplicity.
At dilation `9/100`, keeping that factor excludes every multiple zero in
`Re rho >= 19999/20000` and `log(abs(Im rho)+2) <= 50000`.
The previous signed-pole exclusion pays the heights below `10^6`.
This is an independent arithmetic exclusion
of multiple zeros, not a new all-zero-free region and not the all-height
ceiling. Simple zeros and heights beyond the stated range remain open.

The last theorem transfers this proved multiplicity restriction to the
original source-equivalent joined physical carrier; no mask, order or
carrier is changed, and no new cancellation hypothesis is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingGaussianMultiplicity
open ZetaGaussianScaledBandBudget (width shift gaussianScale)
open ZetaGaussianExpandedScale GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)
open MeasureTheory Set GaussianFermiZeroPair GaussianFermiGaussianMixture

/-- The exact Gaussian tangent also applies at the smaller dilation;
the old `q >= 1` hypothesis is not used as a source estimate here. -/
theorem expanded_tangent_lower {q : ℝ} (hq : 9/100 <= q) (z : ℝ) :
    q * (199350 - 56250*z) <= halfGaussian (gaussianScale q) (width q*z) := by
  have hw := (ZetaGaussianExpandedScale.width_bounds hq).1
  have hs : (443/1000 : ℝ) <= Real.sqrt (Real.pi/4)/2 := by
    have he := Real.sq_sqrt (show 0 <= Real.pi/4 by positivity)
    nlinarith [Real.pi_gt_d2, Real.sqrt_nonneg (Real.pi/4)]
  have ht := halfGaussian_tangent_lower (by norm_num : (0 : ℝ) < 4) z
  have hscale := halfGaussian_scale hw 4 z
  have hB : 4*width q^2 = gaussianScale q := by
    unfold width gaussianScale GaussianStripProfile.gaussianScale
    ring
  rw [hB, mul_comm z] at hscale
  have he : width q*(q*(199350-56250*z)) = 443/1000-z/8 := by
    unfold width GaussianStripProfile.width
    field_simp
    ring
  have hl : width q*(q*(199350-56250*z)) <=
      width q*halfGaussian (gaussianScale q) (width q*z) := by
    rw [he, hscale]
    norm_num only at ht
    linarith
  exact (mul_le_mul_iff_right₀ hw).mp hl

/-- Integrate the exponential tangent at a chosen physical point, rather
than at zero. This strengthens the same positive Gaussian source. -/
theorem halfGaussian_tangent_at_lower {b : ℝ} (hb : 0 < b) (x t₀ : ℝ) :
    Real.exp (-x*t₀)*((1+x*t₀)*Real.sqrt (Real.pi/b)/2-x/(2*b)) <=
      halfGaussian b x := by
  have hi0 : Integrable (window b) := by simpa using integrable_window_exp hb 0
  have hi1 : Integrable (fun t : ℝ => t*window b t) := integrable_mul_exp_neg_mul_sq hb
  have hit := ((hi0.const_mul (1+x*t₀)).sub (hi1.const_mul x)).const_mul
    (Real.exp (-x*t₀))
  have hpoint (t : ℝ) : Real.exp (-x*t₀)*((1+x*t₀)*window b t-x*(t*window b t)) <=
      window b t*Real.exp (-x*t) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x*(t-t₀)))
      (show 0 <= Real.exp (-x*t₀)*window b t from
        mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    have he : Real.exp (-x*t₀)*Real.exp (-x*(t-t₀)) = Real.exp (-x*t) := by
      rw [<-Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (-x*t₀)*window b t)*(1+(-x*(t-t₀))) := by ring
      _ <= (Real.exp (-x*t₀)*window b t)*Real.exp (-x*(t-t₀)) := by
        simpa only [add_comm] using h
      _ = window b t*(Real.exp (-x*t₀)*Real.exp (-x*(t-t₀))) := by ring
      _ = _ := by rw [he]
  have h := integral_mono (hit.integrableOn (s := Ioi (0 : ℝ)))
    (integrable_window_exp hb x).integrableOn hpoint
  rw [integral_const_mul] at h
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hi0.const_mul (1+x*t₀)).integrableOn
      (hi1.const_mul x).integrableOn, integral_const_mul, integral_const_mul,
    integral_half_first_moment hb] at h
  have hz : (∫ t in Ioi (0 : ℝ), window b t) = Real.sqrt (Real.pi/b)/2 := by
    simpa [window] using integral_gaussian_Ioi b
  rw [hz] at h
  simpa only [halfGaussian, mul_div_assoc, mul_one_div] using h

/-- The chosen nonzero tangent gives an exact rational enclosure at the
worst normalized damping in the candidate strip. -/
theorem normalized_source_lower :
    (461567/1875000 : ℝ) <= halfGaussian 4 (1013/500) := by
  have hs : (443/1000 : ℝ) <= Real.sqrt (Real.pi/4)/2 := by
    have he := Real.sq_sqrt (show 0 <= Real.pi/4 by positivity)
    nlinarith [Real.pi_gt_d2, Real.sqrt_nonneg (Real.pi/4)]
  have hlog : (1013/2500 : ℝ) <= Real.log (3/2) := by
    have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) <= 1/5)
      (by norm_num : (1/5 : ℝ) < 1) 3
    norm_num [Finset.sum_range_succ] at h
    linarith
  have he : (2/3 : ℝ) <= Real.exp (-(1013/500)*(1/5)) := by
    have h := Real.exp_le_exp.mpr (neg_le_neg hlog)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3/2)] at h
    norm_num at h ⊢
    exact h
  have hb : (461567/1250000 : ℝ) <=
      (1+(1013/500)*(1/5))*Real.sqrt (Real.pi/4)/2-(1013/500)/(2*4) := by
    nlinarith only [hs]
  have hm := mul_le_mul he hb (by norm_num : (0 : ℝ) <= 461567/1250000)
    (Real.exp_pos _).le
  have ht := halfGaussian_tangent_at_lower (by norm_num : (0 : ℝ) < 4) (1013/500) (1/5)
  norm_num at hm ht ⊢
  exact hm.trans ht

/-- The exact homogeneity transfers the stronger rational enclosure to
the original physical Gaussian scale, without a numerical integration. -/
theorem physical_source_lower :
    (12462309/1250 : ℝ) <=
      halfGaussian (gaussianScale (9/100)) (width (9/100)*(1013/500)) := by
  have hw := (ZetaGaussianExpandedScale.width_bounds (q := 9/100) (by norm_num)).1
  have hs := halfGaussian_scale hw 4 (1013/500)
  have hB : 4*width (9/100)^2 = gaussianScale (9/100) := by
    norm_num [width, gaussianScale, GaussianStripProfile.gaussianScale, GaussianStripProfile.width]
  rw [hB] at hs
  norm_num [width, GaussianStripProfile.width] at hs ⊢
  linarith only [hs, normalized_source_lower]

/-- A double or higher zero in the actual narrow strip supplies this
explicit complete source, including the positive Poisson reserve. -/
theorem selected_multiple_source_lower {a₁ : ℝ} (ha₁ : 79/250 <= a₁)
    (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    984028661/156250 <= a₁ * ((analyticZetaZeroMultiplicity rho : ℝ) *
      (halfGaussian (gaussianScale (9/100)) (1+shift (9/100)-rho.1.re) -
        Real.pi^2*(1+shift (9/100)-rho.1.re)/(8*halfWidth 9 (shift (9/100))^2)) +
      factor 9 (gaussianScale (9/100)) (shift (9/100)) *
        ((analyticZetaZeroMultiplicity rho : ℝ)/(1+shift (9/100)+
          halfWidth 9 (shift (9/100))-rho.1.re))) := by
  have hx := (ZetaGaussianExpandedScale.shift_bounds (q := 9/100) (by norm_num)).1
  have hη := (ZetaGaussianExpandedScale.geometry (q := 9/100) (by norm_num)).1
  have hB := (ZetaGaussianExpandedScale.gaussianScale_bounds (q := 9/100) (by norm_num)).1
  have hd : 0 < 1+shift (9/100)-rho.1.re := by linarith [rho.re_lt_one]
  have he : shift (9/100)+1/20000 = width (9/100)*(1013/500) := by
    norm_num [shift, width, GaussianStripProfile.shift, GaussianStripProfile.width]
  have hdu : 1+shift (9/100)-rho.1.re <= width (9/100)*(1013/500) := by
    rw [<-he]
    linarith
  have hG := physical_source_lower.trans (halfGaussian_antitone hB hdu)
  have hpi : Real.pi^2 <= 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hcot : Real.pi^2*(1+shift (9/100)-rho.1.re)/
      (8*halfWidth 9 (shift (9/100))^2) <= 5 := by
    calc
      _ <= 16*(1/40500000+1/20000)/(8*(1/200 : ℝ)^2) := by
        gcongr
        linarith [(ZetaGaussianExpandedScale.shift_bounds (q := 9/100) (by norm_num)).2]
      _ <= _ := by norm_num
  have hb : (12456059/1250 : ℝ) <=
      halfGaussian (gaussianScale (9/100)) (1+shift (9/100)-rho.1.re) -
        Real.pi^2*(1+shift (9/100)-rho.1.re)/(8*halfWidth 9 (shift (9/100))^2) := by
    linarith only [hG, hcot]
  have hmR : (2 : ℝ) <= analyticZetaZeroMultiplicity rho := by exact_mod_cast hm
  have hweighted := mul_le_mul hmR hb (by norm_num : (0 : ℝ) <= 12456059/1250)
    (by linarith : (0 : ℝ) <= analyticZetaZeroMultiplicity rho)
  have hr : 0 <= factor 9 (gaussianScale (9/100)) (shift (9/100)) *
      ((analyticZetaZeroMultiplicity rho : ℝ)/(1+shift (9/100)+
        halfWidth 9 (shift (9/100))-rho.1.re)) := by
    have hden : 0 < 1+shift (9/100)+halfWidth 9 (shift (9/100))-rho.1.re := by
      linarith
    unfold factor
    positivity
  have ht : (12456059/625 : ℝ) <= (analyticZetaZeroMultiplicity rho : ℝ) *
      (halfGaussian (gaussianScale (9/100)) (1+shift (9/100)-rho.1.re) -
        Real.pi^2*(1+shift (9/100)-rho.1.re)/(8*halfWidth 9 (shift (9/100))^2)) +
      factor 9 (gaussianScale (9/100)) (shift (9/100)) *
        ((analyticZetaZeroMultiplicity rho : ℝ)/(1+shift (9/100)+
          halfWidth 9 (shift (9/100))-rho.1.re)) := by
    linarith only [hweighted, hr]
  have hp := mul_le_mul ha₁ ht (by norm_num : (0 : ℝ) <= 12456059/625)
    (by linarith : 0 <= a₁)
  norm_num at hp
  exact hp

/-- A rational complete-budget ceiling at logarithmic height 50000.
The use of `log L <= 11` is proved, not numerically sampled. -/
theorem complete_cost_lt_source {L : ℝ} (hL : 1 <= L) (hLu : L <= 50000) :
    36922*(9/100 : ℝ)+L/35+57*Real.log L+840 < 984028661/156250 := by
  have hl : Real.log L <= 11 := by
    apply (Real.log_le_iff_le_exp (by linarith : 0 < L)).mpr
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) <= 27/10)
      (show (27/10 : ℝ) <= Real.exp 1 by linarith [Real.exp_one_gt_d9]) 11
    rw [<-Real.exp_nat_mul] at hp
    norm_num at hp
    linarith
  linarith

/-- Actual multiple zeros are excluded by the unchanged complete Gaussian
arithmetic budget throughout this enlarged height interval. -/
theorem family_no_multiple {a ω : ℕ -> ℝ} (ha : ∀ n, 0 <= a n) (hs : Summable a)
    (hp : ∀ t, 0 <= zetaPhaseKernel a ω t) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 -> 1 <= ω n)
    (hlog : Summable (fun n => tail a n*Real.log (ω n)))
    (ha0 : a 0 <= 37/200) (ha1 : 79/250 <= a 1)
    (hW : mass a <= 61/100) (hF : frequencyCost a ω <= 1/4)
    (rho : NontrivialZetaZero) (ht : 1000000 <= |rho.1.im|)
    (hLu : scale rho.1.im <= 50000) (hnear : 1-rho.1.re <= 1/20000)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) : False := by
  have hq : (9/100 : ℝ) <= 9/100 := le_refl _
  obtain ⟨hx, hxu⟩ := ZetaGaussianExpandedScale.shift_bounds hq
  have hx' : shift (9/100) <= delta 9/4 := hxu.trans
    (by norm_num [delta, DerivativePowerExponents.alpha])
  have hline : DirichletPowerParameters.line 9 < rho.1.re := by
    have hd : (1/20000 : ℝ) < delta 9 := by norm_num [delta, DerivativePowerExponents.alpha]
    rw [delta_eq_one_sub_line] at hd
    linarith
  have hscale := ZetaGaussianBandBudget.scale_lower ht
  have h := gaussian_source_le_budget ha hs hp hω0 hω1 hω hlog 9 (by norm_num)
    (ZetaGaussianExpandedScale.gaussianScale_bounds hq).1 hx hx' rho (by linarith) hscale hline
  have hb := ZetaGaussianExpandedCost.budget_le (ha 0) ha0 (tsum_nonneg (tail_nonneg ha))
    hW hF hq ht
  have hl := selected_multiple_source_lower ha1 rho hnear hm
  have hc := complete_cost_lt_source hscale hLu
  linarith only [h, hb, hl, hc]

/-- No exposure, simplicity, short-interval or new prime-cancellation
hypothesis is used: the exact contact family discharges every premise. -/
theorem simple_of_narrow_strip_log_height (rho : NontrivialZetaZero)
    (ht : 1000000 <= |rho.1.im|) (hLu : scale rho.1.im <= 50000)
    (hnear : 1-rho.1.re <= 1/20000) : analyticZetaZeroMultiplicity rho = 1 := by
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
      rho ht hLu hnear hm
  have hp := analyticZetaZeroMultiplicity_positive rho
  omega

/-- Retain the existing signed-pole exclusion below the Gaussian starting
height, so the new multiplicity restriction has no lower-height gap. -/
theorem simple_of_narrow_strip_up_to_log_height (rho : NontrivialZetaZero)
    (hLu : scale rho.1.im <= 50000) (hnear : 1-rho.1.re <= 1/20000) :
    analyticZetaZeroMultiplicity rho = 1 := by
  by_cases ht : 1000000 <= |rho.1.im|
  · exact simple_of_narrow_strip_log_height rho ht hLu hnear
  have hsmall : |rho.1.im| <= 1000000 := le_of_lt (lt_of_not_ge ht)
  have hlog : Real.log (|rho.1.im|+2) <= 20 := by
    have h := Real.log_le_log (by positivity : 0 < |rho.1.im|+2)
      (show |rho.1.im|+2 <= (2 : ℝ)^20 by norm_num; linarith)
    rw [Real.log_pow] at h
    have htwo : Real.log 2 <= 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num at h
    linarith
  have hw : (1/20000 : ℝ) < zetaSignedPoleZeroMargin rho.1.im := by
    unfold zetaSignedPoleZeroMargin
    apply (lt_div_iff₀ (zetaSignedPole_denominator_pos rho.1.im)).mpr
    linarith
  have hr := zetaSignedPole_margin_lt_one_sub_re rho
  exfalso
  linarith only [hw, hr, hnear]

/-- An unconditional horizontal restriction on EVERY multiple actual
zero in this height range; no exposed-zero hypothesis is present. -/
theorem multiple_zero_re_lt (rho : NontrivialZetaZero)
    (hLu : scale rho.1.im <= 50000) (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    rho.1.re < 19999/20000 := by
  by_contra! hnear
  have hs := simple_of_narrow_strip_up_to_log_height rho hLu
    (by linarith : 1-rho.1.re <= 1/20000)
  omega

/-- The SAME joined physical carrier satisfies the current ceiling in
the newly paid multiplicity range. Exposure is used only to transfer its
existing source; the multiplicity payment above is independent of it. -/
theorem eventually_joinedPhysical_ceiling_in_height_range (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho ->
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling)
    (hLu : scale rho.1.im <= 50000) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re < 42/25 := by
  have hnear : 1-rho.1.re <= 1/20000 := by
    norm_num only [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith
  have hm := simple_of_narrow_strip_up_to_log_height rho hLu hnear
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  simp only [hm, Nat.cast_one, one_pow, one_mul, Complex.add_re, Complex.neg_re,
    Complex.one_re, Complex.ofReal_re] at hs
  have hu : 1/2 <= 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hc := ZetaRieszEndgameSlack.retainedCost_upper hu hU
  exact hs.eventually (gt_mem_nhds (show -1+ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) <
    42/25 by linarith only [hc]))

end RiemannGaussian.ZetaRieszCeilingGaussianMultiplicity
