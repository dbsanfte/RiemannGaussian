/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingSharpMultiplicity

/-!
# A quantitative all-height bound for the whole signed carrier

The complete Gaussian arithmetic inequality bounds the actual analytic
multiplicity, not an anonymous cofactor allowance. Keeping this factor gives
an explicit height-dependent ceiling for the SAME native joinedPhysical
carrier in the entire original fixed strip. Two complete Gaussian tests are
joined by taking their smaller multiplicity cap.

This is not the required height-independent ceiling 42/25. The all-family
positive-budget obstruction remains valid, and the full endgame remains open.
No mask, phase, order, diagonal, count or arithmetic carrier is changed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Complex Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingWholeHeightBound
open ZetaGaussianScaledBandBudget (width shift gaussianScale)
open ZetaGaussianExpandedScale GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)

/-- The second actual Gaussian moment gives a rational lower bound at
every damping. The signed recurrence is combined before any estimate. -/
theorem halfGaussian_lower_second_moment (x : ℝ) :
    x/(x^2+2) <= halfGaussian 1 x := by
  have hpos : (0 : ℝ) <= GaussianHalfLaplaceMoments.moment 2 x := by
    unfold GaussianHalfLaplaceMoments.moment
    apply integral_nonneg
    intro t
    unfold GaussianHalfLaplaceMoments.atom GaussianFermiZeroPair.window
    positivity
  have h1 := GaussianHalfLaplaceMoments.moment_one x
  have h2 := GaussianHalfLaplaceMoments.moment_recurrence 0 x
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd, one_mul] at h2
  have hx := congrArg (fun v : ℝ => x*v) h1
  apply (div_le_iff₀ (by nlinarith [sq_nonneg x] : 0 < x^2+2)).mpr
  rw [<-GaussianHalfLaplaceMoments.moment_zero]
  nlinarith only [hpos, hx, h2]

/-- A complete rational Gaussian source bound at dilation one. -/
theorem physical_source_lower :
    (19650 : ℝ) <= halfGaussian (gaussianScale 1) (1/20000+shift 1) := by
  have hG := halfGaussian_lower_second_moment (22501/2000)
  have hs := halfGaussian_scale (r := 2) (by norm_num) 1 (22501/2000)
  norm_num at hs hG
  have hw : (0 : ℝ) < width 1 := by norm_num [width, GaussianStripProfile.width]
  have ht := halfGaussian_scale hw 4 (22501/1000)
  norm_num [width, shift, gaussianScale, GaussianStripProfile.width,
    GaussianStripProfile.shift, GaussianStripProfile.gaussianScale] at ht ⊢
  linarith only [hs, hG, ht]

/-- The full selected Gaussian source is linear in ACTUAL multiplicity.
The Poisson reserve is nonnegative and the cotangent correction is paid. -/
theorem selected_source_lower {a₁ q price : ℝ} (ha₁ : 79/250 <= a₁)
    (hq : 9/100 <= q) (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hprice0 : 0 < price)
    (hprice : price <= (79/250)*
      (halfGaussian (gaussianScale q) (1/20000+shift q)-5)) :
    price*(analyticZetaZeroMultiplicity rho : ℝ) <=
      a₁ * ((analyticZetaZeroMultiplicity rho : ℝ) *
        (halfGaussian (gaussianScale q) (1+shift q-rho.1.re) -
          Real.pi^2*(1+shift q-rho.1.re)/(8*halfWidth 9 (shift q)^2)) +
        factor 9 (gaussianScale q) (shift q) *
          ((analyticZetaZeroMultiplicity rho : ℝ)/(1+shift q+
            halfWidth 9 (shift q)-rho.1.re))) := by
  have hx := (ZetaGaussianExpandedScale.shift_bounds hq).1
  have hη := (ZetaGaussianExpandedScale.geometry hq).1
  have hB := (ZetaGaussianExpandedScale.gaussianScale_bounds hq).1
  have hd : 0 < 1+shift q-rho.1.re := by linarith [rho.re_lt_one]
  have hdu : 1+shift q-rho.1.re <= 1/20000+shift q := by linarith
  have hG := halfGaussian_antitone hB hdu
  have hpi : Real.pi^2 <= 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hcot : Real.pi^2*(1+shift q-rho.1.re)/
      (8*halfWidth 9 (shift q)^2) <= 5 := by
    calc
      _ <= 16*(1/40500000+1/20000)/(8*(1/200 : ℝ)^2) := by
        gcongr
        linarith [(ZetaGaussianExpandedScale.shift_bounds hq).2]
      _ <= _ := by norm_num
  have hm : (0 : ℝ) <= analyticZetaZeroMultiplicity rho := Nat.cast_nonneg _
  have hr : 0 <= factor 9 (gaussianScale q) (shift q) *
      ((analyticZetaZeroMultiplicity rho : ℝ)/(1+shift q+
        halfWidth 9 (shift q)-rho.1.re)) := by
    have hden : 0 < 1+shift q+halfWidth 9 (shift q)-rho.1.re := by
      linarith [rho.re_lt_one]
    unfold factor
    positivity
  have hbase : 0 <= halfGaussian (gaussianScale q) (1/20000+shift q)-5 := by
    linarith only [hprice, hprice0]
  have hb : halfGaussian (gaussianScale q) (1/20000+shift q)-5 <=
      halfGaussian (gaussianScale q) (1+shift q-rho.1.re)-
        Real.pi^2*(1+shift q-rho.1.re)/(8*halfWidth 9 (shift q)^2) := by
    linarith only [hG, hcot]
  have hw := mul_le_mul_of_nonneg_left hb hm
  have ht := le_trans hw (le_add_of_nonneg_right hr)
  have ha := mul_le_mul ha₁ ht (mul_nonneg hm hbase) (by linarith : 0 <= a₁)
  have hp := mul_le_mul_of_nonneg_right hprice hm
  nlinarith only [ha, hp]

/-- The COMPLETE existing arithmetic cost, with its height term explicit. -/
def cost (q L : ℝ) : ℝ := 36922*q+L/35+57*Real.log L+840

/-- The previously proved small-dilation price per actual multiplicity. -/
def smallUnit : ℝ := 984028661/312500

/-- The new large-dilation price per actual multiplicity. -/
def wideUnit : ℝ := 6200

/-- Every arithmetic hypothesis is discharged by the exact contact family.
No exposure, cofactor density, phase randomness or bilinear hypothesis enters. -/
theorem actual_multiplicity_price_le_cost {q price : ℝ}
    (hq : 9/100 <= q) (rho : NontrivialZetaZero)
    (ht : 1000000 <= |rho.1.im|) (hnear : 1-rho.1.re <= 1/20000)
    (hprice0 : 0 < price)
    (hprice : price <= (79/250)*
      (halfGaussian (gaussianScale q) (1/20000+shift q)-5)) :
    price*(analyticZetaZeroMultiplicity rho : ℝ) <= cost q (scale rho.1.im) := by
  have h0 : phaseContactExactFamily 0 = phaseContactExactCoefficients 0 := by
    simpa [phaseContactExactFamily, phaseContactFrequency] using
      phaseContactFrequencyFamily_apply phaseContactExactCoefficients 0
  have h1 : phaseContactExactFamily 1 = phaseContactExactCoefficients 1 := by
    simpa [phaseContactExactFamily, phaseContactFrequency] using
      phaseContactFrequencyFamily_apply phaseContactExactCoefficients 1
  have ha1 : 79/250 <= phaseContactExactFamily 1 := by
    rw [h1]
    exact GaussianFermiProfileSurplus.exact_first_lower
  obtain ⟨hx,hxu⟩ := ZetaGaussianExpandedScale.shift_bounds hq
  have hx' : shift q <= delta 9/4 := hxu.trans
    (by norm_num [delta, DerivativePowerExponents.alpha])
  have hline : DirichletPowerParameters.line 9 < rho.1.re := by
    have hd : (1/20000 : ℝ) < delta 9 := by
      norm_num [delta, DerivativePowerExponents.alpha]
    rw [delta_eq_one_sub_line] at hd
    linarith
  have h := gaussian_source_le_budget phaseContactExactFamily_nonneg
    ZetaExactPhaseAngularExclusion.exact_summable phaseContactExactFamily_kernel_nonneg
    (by norm_num) (by norm_num)
    (fun n hn => by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    ZetaExactPhaseAngularExclusion.exact_log_summable 9 (by norm_num)
    (ZetaGaussianExpandedScale.gaussianScale_bounds hq).1 hx hx' rho (by linarith)
    (ZetaGaussianBandBudget.scale_lower ht) hline
  have hb := ZetaGaussianExpandedCost.budget_le (phaseContactExactFamily_nonneg 0)
    (show phaseContactExactFamily 0 <= 37/200 by
      rw [h0]; exact GaussianFermiProfileSurplus.exact_constant_upper)
    (tsum_nonneg (tail_nonneg phaseContactExactFamily_nonneg))
    ZetaExactPhaseAngularExclusion.mass_bounds.2
    ZetaGaussianBandExclusion.exact_frequency_cost hq ht
  exact (selected_source_lower ha1 hq rho hnear hprice0 hprice).trans
    (h.trans hb)

/-- A complete multiplicity bound from the small Gaussian, at every eligible height. -/
theorem small_price (rho : NontrivialZetaZero) (ht : 1000000 <= |rho.1.im|)
    (hnear : 1-rho.1.re <= 1/20000) :
    smallUnit*(analyticZetaZeroMultiplicity rho : ℝ) <= cost (9/100) (scale rho.1.im) := by
  apply actual_multiplicity_price_le_cost (by norm_num) rho ht hnear
    (by norm_num [smallUnit])
  have he : 1/20000+shift (9/100) = width (9/100)*(1013/500) := by
    norm_num [shift, width, GaussianStripProfile.shift, GaussianStripProfile.width]
  rw [he]
  unfold smallUnit
  linarith only [ZetaRieszCeilingGaussianMultiplicity.physical_source_lower]

/-- The wider Gaussian improves the leading height price per multiplicity. -/
theorem wide_price (rho : NontrivialZetaZero) (ht : 1000000 <= |rho.1.im|)
    (hnear : 1-rho.1.re <= 1/20000) :
    wideUnit*(analyticZetaZeroMultiplicity rho : ℝ) <= cost 1 (scale rho.1.im) := by
  apply actual_multiplicity_price_le_cost (by norm_num) rho ht hnear
    (by norm_num [wideUnit])
  unfold wideUnit
  linarith only [physical_source_lower]

/-- Taking the better COMPLETE certificate retains the previously paid
low-height simplicity layer and covers the entire original fixed strip. -/
def heightCap (L : ℝ) : ℝ :=
  if L <= 60000 then 1 else min (cost (9/100) L/smallUnit) (cost 1 L/wideUnit)

/-- An independent arithmetic bound for every actual zero in the original
strip, with NO upper-height restriction and NO exposure premise. -/
theorem multiplicity_le_heightCap (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000) :
    (analyticZetaZeroMultiplicity rho : ℝ) <= heightCap (scale rho.1.im) := by
  by_cases hL : scale rho.1.im <= 60000
  · have hn : 1-rho.1.re <= ZetaRieszCeilingSharpMultiplicity.simplicityWidth rho.1.im := by
      rw [ZetaRieszCeilingSharpMultiplicity.simplicityWidth_eq_fixed hL]
      exact hnear
    have hm := ZetaRieszCeilingSharpMultiplicity.simple_of_boundary_layer rho hn
    simp [heightCap,hL,hm]
  have ht : 1000000 <= |rho.1.im| := by
    by_contra! ht
    have hh := Real.log_le_log (by positivity : 0 < |rho.1.im|+2)
      (show |rho.1.im|+2 <= (2 : ℝ)^20 by norm_num; linarith)
    rw [Real.log_pow] at hh
    have htwo : Real.log 2 <= 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num at hh
    have hscale : scale rho.1.im <= 20 := by
      change Real.log (|rho.1.im|+2) <= 20
      linarith
    linarith
  rw [heightCap,if_neg hL,le_min_iff]
  constructor
  · apply (le_div_iff₀ (by norm_num [smallUnit] : 0 < smallUnit)).mpr
    simpa only [mul_comm] using small_price rho ht hnear
  · apply (le_div_iff₀ (by norm_num [wideUnit] : 0 < wideUnit)).mpr
    simpa only [mul_comm] using wide_price rho ht hnear

/-- A bound for the WHOLE signed source. The height cost remains visible. -/
def signedCeiling (u L : ℝ) : ℝ :=
  -heightCap L+ZetaRieszMaskSupport.retainedCost u*(heightCap L)^2

/-- The actual arithmetic multiplicity cap bounds the complete source
polynomial monotonically. There is no sectorwise or absolute carrier debit. -/
theorem source_le_signedCeiling (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hu : 1/2 <= 3/2-rho.1.re)
    (hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling) :
    -(analyticZetaZeroMultiplicity rho : ℝ)+
        (analyticZetaZeroMultiplicity rho : ℝ)^2*
          ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) <=
      signedCeiling (3/2-rho.1.re) (scale rho.1.im) := by
  have hm : (1 : ℝ) <= analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hM := multiplicity_le_heightCap rho hnear
  have hC := ZetaRieszJointFloor.retainedCost_gt_nine_tenths hu hU
  have hsum : (2 : ℝ) <= heightCap (scale rho.1.im)+analyticZetaZeroMultiplicity rho := by
    linarith
  have hf := mul_le_mul_of_nonneg_left hsum
    (show 0 <= ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) by linarith)
  have hh : 0 <= ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re)*
      (heightCap (scale rho.1.im)+analyticZetaZeroMultiplicity rho)-1 := by
    linarith
  have hp := mul_nonneg (sub_nonneg.mpr hM) hh
  unfold signedCeiling
  nlinarith only [hp]

/-- At EVERY fixed height and throughout the ORIGINAL fixed radius strip,
the native signed carrier has an explicit cofinal upper bound. The price
depends on height and does NOT establish the height-independent 42/25 target.
Exposure is used only for the existing, unchanged source transfer. -/
theorem eventually_joinedPhysical_height_ceiling (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho ->
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re <
        signedCeiling (3/2-rho.1.re) (scale rho.1.im)+ε := by
  have hnear : 1-rho.1.re <= 1/20000 := by
    norm_num only [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith
  have hu : 1/2 <= 3/2-rho.1.re := by linarith [rho.re_lt_one]
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  have hbound := source_le_signedCeiling rho hnear hu hU
  have hg : (-(analyticZetaZeroMultiplicity rho : ℂ)+
      (analyticZetaZeroMultiplicity rho : ℂ)^2*
        (ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) : ℂ)).re <
      signedCeiling (3/2-rho.1.re) (scale rho.1.im)+ε := by
    norm_num only [Complex.add_re,Complex.neg_re,pow_two,Complex.mul_re,
      Complex.natCast_re,Complex.natCast_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    nlinarith only [hbound,hε]
  simpa only [Function.comp_apply] using hs.eventually (gt_mem_nhds hg)

/-- The small-dilation full signed price, used ONLY as a comparison bound.
This is not a new carrier and is not a constant ceiling. -/
def smallCeiling (u L : ℝ) : ℝ :=
  -(cost (9/100) L/smallUnit)+ZetaRieszMaskSupport.retainedCost u*
    (cost (9/100) L/smallUnit)^2

/-- A rational, genuinely all-large-height improvement in the multiplicity
price. The complete logarithmic height term stays on both sides. -/
theorem wideCap_le_four_sevenths_small {L : ℝ} (hL : 10000000 <= L) :
    cost 1 L/wideUnit <= (4/7)*(cost (9/100) L/smallUnit) := by
  have hl : 0 <= Real.log L := Real.log_nonneg (by linarith)
  unfold cost wideUnit smallUnit
  linarith only [hL,hl]

/-- The WHOLE signed source price improves by at least 33/49 once the
logarithmic height is at least ten million. These are comparison-price
units, not a progress percentage toward the constant 42/25 endgame. -/
theorem signedCeiling_le_reduced_small {u L : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) (hL : 10000000 <= L) :
    signedCeiling u L <= (16/49)*smallCeiling u L := by
  have hl : 0 <= Real.log L := Real.log_nonneg (by linarith)
  have hc := ZetaRieszJointFloor.retainedCost_gt_nine_tenths hu hU
  have hsmall : 1 <= cost (9/100) L/smallUnit := by
    apply (le_div_iff₀ (by norm_num [smallUnit] : 0 < smallUnit)).mpr
    unfold cost smallUnit
    linarith only [hL,hl]
  have hwide : 1 <= cost 1 L/wideUnit := by
    apply (le_div_iff₀ (by norm_num [wideUnit] : 0 < wideUnit)).mpr
    unfold cost wideUnit
    linarith only [hL,hl]
  have hcap : 1 <= heightCap L := by
    rw [heightCap,if_neg (show ¬ L <= 60000 by linarith),le_min_iff]
    exact ⟨hsmall,hwide⟩
  have hcapu : heightCap L <= (4/7)*(cost (9/100) L/smallUnit) := by
    rw [heightCap,if_neg (show ¬ L <= 60000 by linarith)]
    exact min_le_right _ _ |>.trans (wideCap_le_four_sevenths_small hL)
  have hs : 2 <= heightCap L+(4/7)*(cost (9/100) L/smallUnit) := by linarith
  have hcoef := mul_le_mul_of_nonneg_left hs
    (show 0 <= ZetaRieszMaskSupport.retainedCost u by linarith)
  have hf : 0 <= ZetaRieszMaskSupport.retainedCost u*
      (heightCap L+(4/7)*(cost (9/100) L/smallUnit))-1 := by linarith
  have hp := mul_nonneg (sub_nonneg.mpr hcapu) hf
  unfold signedCeiling smallCeiling
  nlinarith only [hp,hsmall]

/-- A quantitative ceiling saving for the entire literal carrier, not
just selected populations. The comparison price still grows with height. -/
theorem eventually_joinedPhysical_reduced_ceiling (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho ->
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : 10000000 <= scale rho.1.im) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re <
        (16/49)*smallCeiling (3/2-rho.1.re) (scale rho.1.im)+ε := by
  have hu : 1/2 <= 3/2-rho.1.re := by linarith [rho.re_lt_one]
  filter_upwards [eventually_joinedPhysical_height_ceiling rho hrho hexposed hU hε] with j hj
  have hb := signedCeiling_le_reduced_small hu hU hL
  linarith only [hj,hb]

/-- Integrality matters: the complete price is below THREE actual source
units throughout this interval, even where a double source is not excluded. -/
theorem heightCap_lt_three {L : ℝ} (hLu : L <= 160000) : heightCap L < 3 := by
  by_cases hL : L <= 60000
  · simp [heightCap,hL]
  have hl : Real.log L <= 12 := by
    apply (Real.log_le_iff_le_exp (by linarith : 0 < L)).mpr
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) <= 2718/1000)
      (show (2718/1000 : ℝ) <= Real.exp 1 by linarith [Real.exp_one_gt_d9]) 12
    rw [<-Real.exp_nat_mul] at hp
    norm_num at hp
    linarith
  have hp : cost (9/100) L/smallUnit < 3 := by
    apply (div_lt_iff₀ (by norm_num [smallUnit] : 0 < smallUnit)).mpr
    unfold cost smallUnit
    linarith only [hLu,hl]
  rw [heightCap,if_neg hL]
  exact (min_le_left _ _).trans_lt hp

/-- Every actual candidate in the ORIGINAL fixed strip has multiplicity
at most two up to logarithmic height 160000. No exposure assumption enters. -/
theorem multiplicity_le_two_in_height_range (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000) (hLu : scale rho.1.im <= 160000) :
    analyticZetaZeroMultiplicity rho <= 2 := by
  have hm := (multiplicity_le_heightCap rho hnear).trans_lt (heightCap_lt_three hLu)
  have hn : analyticZetaZeroMultiplicity rho < 3 := by exact_mod_cast hm
  omega

/-- A genuinely numerical ceiling for the WHOLE native carrier on this
larger height interval. It is 1.6808, still 0.0008 ABOVE the required 1.68;
it is not a zero exclusion or the full all-height constant ceiling. -/
theorem eventually_joinedPhysical_near_ceiling (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho ->
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling)
    (hLu : scale rho.1.im <= 160000) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re < 2101/1250 := by
  have hnear : 1-rho.1.re <= 1/20000 := by
    norm_num only [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith
  have hu : 1/2 <= 3/2-rho.1.re := by linarith [rho.re_lt_one]
  have hm := multiplicity_le_two_in_height_range rho hnear hLu
  have hpos := analyticZetaZeroMultiplicity_positive rho
  have hc := ZetaRieszEndgameSlack.retainedCost_upper hu hU
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  have hreal : (-(analyticZetaZeroMultiplicity rho : ℂ)+
      (analyticZetaZeroMultiplicity rho : ℂ)^2*
        (ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) : ℂ)).re =
      -(analyticZetaZeroMultiplicity rho : ℝ)+(analyticZetaZeroMultiplicity rho : ℝ)^2*
        ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) := by norm_cast
  have hg : (-(analyticZetaZeroMultiplicity rho : ℂ)+
      (analyticZetaZeroMultiplicity rho : ℂ)^2*
        (ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) : ℂ)).re < 2101/1250 := by
    rw [hreal]
    rcases (show analyticZetaZeroMultiplicity rho = 1 ∨
      analyticZetaZeroMultiplicity rho = 2 by omega) with h | h
    · norm_num only [h,Nat.cast_one,one_pow,one_mul]
      linarith only [hc]
    · norm_num only [h,Nat.cast_ofNat,pow_two]
      linarith only [hc]
  simpa only [Function.comp_apply] using hs.eventually (gt_mem_nhds hg)

end RiemannGaussian.ZetaRieszCeilingWholeHeightBound
