/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaElevenZeroCompleteness
import RiemannGaussian.ZetaRieszPrimePairConvolution
import RiemannGaussian.ZetaGlobalSignedBudget
import RiemannGaussian.GaussianDigammaGrowth
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# A shifted-center filter on individual factorial prime legs

The order is unchanged. The arithmetic multiplier is exactly
`1-C^k/p`, while the two generating-function pole terms cancel.
No hard-share packet transfer is inferred from these identities.
-/

namespace RiemannGaussian.ZetaRieszShiftedCenter
noncomputable section
open Complex Filter Set Topology
open scoped BigOperators Classical
open ZetaExposedPrimeMoments ZetaRieszPrimePairConvolution

/-- The original safe center. -/
def center (y : ℝ) : ℂ := 3/2+Complex.I*y

/-- The actual pole denominator, including its ordinate. -/
def pole (y : ℝ) : ℂ := center y-1

/-- The exact ratio aligning the shifted and unshifted pole terms. -/
def ratio (y : ℝ) : ℂ := center y/pole y

theorem height_gt_fiftyFour (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    54 < |rho.1.im| := by
  by_contra! h
  linarith [ZetaElevenZeroCompleteness.critical_line_through_fiftyFour rho h]

theorem pole_ne_zero (y : ℝ) : pole y ≠ 0 := by
  apply Complex.ne_zero_of_re_pos
  norm_num [pole, center]

theorem center_ne_zero (y : ℝ) : center y ≠ 0 := by
  apply Complex.ne_zero_of_re_pos
  norm_num [center]

theorem ratio_ne_zero (y : ℝ) : ratio y ≠ 0 := div_ne_zero (center_ne_zero y) (pole_ne_zero y)

theorem ratio_mul_pole (y : ℝ) : ratio y*pole y = center y := by
  exact div_mul_cancel₀ _ (pole_ne_zero y)

theorem norm_ratio_lt {y : ℝ} (hy : 54 < |y|) : ‖ratio y‖ < 1001/1000 := by
  have hp : 0 < ‖pole y‖ := norm_pos_iff.mpr (pole_ne_zero y)
  have hc : ‖center y‖^2 = y^2+9/4 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center, Complex.normSq_apply]
    ring
  have hd : ‖pole y‖^2 = y^2+1/4 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [pole, center, Complex.normSq_apply]
    ring
  have hy2 : 54^2 < y^2 := by nlinarith [sq_abs y]
  rw [ratio, norm_div, div_lt_iff₀ hp]
  nlinarith [norm_nonneg (center y)]

/-- Both the shifted full series and its completed zero term stay in
the Euler half-plane on the entire closed disk of radius two. -/
theorem shifted_re_gt_one {u y : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 10001/20000)
    (hy : 54 < |y|) {t : ℂ} (ht : ‖t‖ ≤ 2) :
    1 < (center y+1-(u : ℂ)*ratio y*t).re := by
  have hC := norm_ratio_lt hy
  have hn : ‖(u : ℂ)*ratio y*t‖ ≤ (10001/20000 : ℝ)*(1001/1000)*2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
    gcongr
  have hr := Complex.re_le_norm ((u : ℂ)*ratio y*t)
  have hc : (center y).re = 3/2 := by simp [center]
  rw [Complex.sub_re, Complex.add_re, hc, Complex.one_re]
  linarith

theorem original_re_pos {u y : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 10001/20000)
    {t : ℂ} (ht : ‖t‖ ≤ 2) : 0 < (center y-(u : ℂ)*t).re := by
  have hn : ‖(u : ℂ)*t‖ ≤ (10001/20000 : ℝ)*2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
    gcongr
  have hr := Complex.re_le_norm ((u : ℂ)*t)
  have hc : (center y).re = 3/2 := by simp [center]
  rw [Complex.sub_re, hc]
  linarith

/-- Exact cancellation, including the totalized common singular point.
Analytic use is restricted separately to the regular working disk. -/
theorem pole_cancellation (u y : ℝ) (t : ℂ) :
    (u : ℂ)/(pole y-u*t)-(u : ℂ)*ratio y/(center y-u*ratio y*t) = 0 := by
  have he : center y-(u : ℂ)*ratio y*t = ratio y*(pole y-u*t) := by
    rw [mul_sub, ratio_mul_pole]
    ring
  rw [he]
  by_cases hz : pole y-(u : ℂ)*t = 0
  · simp [hz]
  · field_simp [ratio_ne_zero y, hz]
    ring

theorem kernel_shift (k p : ℕ) (s : ℂ) (hp : 0 < p) :
    zetaPrimeLogKernel k (s+1) p = zetaPrimeLogKernel k s p/(p : ℂ) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have he : Complex.exp (-(Real.log p : ℂ)) = (p : ℂ)⁻¹ := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hpR]
    simp only [Complex.ofReal_natCast]
  unfold zetaPrimeLogKernel zetaPrimeFeature
  rw [show -((s+1)*(Real.log p : ℂ)) = -(s*(Real.log p : ℂ)) + -(Real.log p : ℂ) by ring,
    Complex.exp_add, he]
  ring

/-- One individual prime leg, before any prime summation or share mask. -/
def leg (u y : ℝ) (k p : ℕ) : ℂ :=
  (k : ℂ)*(u : ℂ)^k*(zetaPrimeLogKernel k (center y) p-
    ratio y^k*zetaPrimeLogKernel k (center y+1) p)

theorem leg_eq_multiplier (u y : ℝ) (k p : ℕ) (hp : 0 < p) :
    leg u y k p = (1-ratio y^k/(p : ℂ))*
      ((k : ℂ)*(u : ℂ)^k*zetaPrimeLogKernel k (center y) p) := by
  rw [leg, kernel_shift k p _ hp]
  ring

/-- The same finite prime set is used at both centers. -/
def finiteLeg (A : Finset ℕ) (u y : ℝ) (k : ℕ) : ℂ :=
  (k : ℂ)*(u : ℂ)^k*(finiteMoment A k (center y)-
    ratio y^k*finiteMoment A k (center y+1))

/-- Complete ordinary-prime legs; genuine convergence follows from
both centers lying in the Euler half-plane. -/
def completeLeg (u y : ℝ) (k : ℕ) : ℂ :=
  (k : ℂ)*(u : ℂ)^k*(ordinaryPrimeMoment k (center y)-
    ratio y^k*ordinaryPrimeMoment k (center y+1))

/-- Full von Mangoldt counterpart, with the positive order indexed as n+1. -/
def fullLeg (u y : ℝ) (n : ℕ) : ℂ :=
  (u : ℂ)^(n+1)*(zetaPrimeLogMoment n (center y)-
    ratio y^(n+1)*zetaPrimeLogMoment n (center y+1))

/-- The meromorphic generating-function expression before pole cancellation. -/
def fullGenerating (u y : ℝ) (t : ℂ) : ℂ :=
  (u : ℂ)*(-logDeriv riemannZeta (center y-u*t))-
    (u : ℂ)*ratio y*(-logDeriv riemannZeta (center y+1-u*ratio y*t))

theorem finiteLeg_eq_sum (A : Finset ℕ) (u y : ℝ) (k : ℕ) :
    finiteLeg A u y k = ∑ p ∈ A, leg u y k p := by
  simp only [finiteLeg, finiteMoment, leg, mul_sub, Finset.mul_sum,
    Finset.sum_sub_distrib]

theorem completeLeg_succ (u y : ℝ) (n : ℕ) :
    completeLeg u y (n+1) = (u : ℂ)^(n+1)*
      (zetaOrdinaryPrimeLogMoment n (center y)-
        ratio y^(n+1)*zetaOrdinaryPrimeLogMoment n (center y+1)) := by
  rw [completeLeg, ordinaryPrimeMoment_succ (by norm_num [center]),
    ordinaryPrimeMoment_succ (by norm_num [center])]
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]

theorem hasSum_completeLeg (u y : ℝ) (k : ℕ) :
    HasSum (fun p : ℕ => if p.Prime then leg u y k p else 0) (completeLeg u y k) := by
  have h := ((summable_ordinaryPrimeMoment (s := center y) (by norm_num [center]) k).hasSum.sub
    (((summable_ordinaryPrimeMoment (s := center y+1) (by norm_num [center]) k).hasSum).mul_left
      (ratio y^k))).mul_left ((k : ℂ)*(u : ℂ)^k)
  change HasSum _ (completeLeg u y k) at h
  apply h.congr_fun
  intro p
  by_cases hp : p.Prime <;> simp [hp, leg]

/-- The only remainder after removing the unshifted genuine xi divisor.
There are no locally reflected zero modes in this definition. -/
def regularGenerating (u y : ℝ) (t : ℂ) : ℂ :=
  (u : ℂ)*zetaGlobalRegularCorrection (center y-u*t)-
    (u : ℂ)*ratio y*zetaGlobalRegularCorrection (center y+1-u*ratio y*t)+
    (u : ℂ)*ratio y*logDeriv riemannXi (center y+1-u*ratio y*t)

theorem global_decomposition {u y : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 10001/20000)
    (hy : 54 < |y|) {t : ℂ} (ht : ‖t‖ ≤ 2)
    (h1 : center y-(u : ℂ)*t ≠ 1)
    (hz : riemannZeta (center y-(u : ℂ)*t) ≠ 0) :
    fullGenerating u y t = -(u : ℂ)*logDeriv riemannXi (center y-u*t)+
      regularGenerating u y t := by
  have hA := logDeriv_riemannXi_of_re_pos_of_riemannZeta_ne_zero
    (original_re_pos hu0 hu ht) h1 hz
  have hB := zeta_global_complex_budget (shifted_re_gt_one hu0 hu hy ht)
  have hp := pole_cancellation u y t
  simp only [pole] at hp
  have hden : center y+1-(u : ℂ)*ratio y*t-1 = center y-u*ratio y*t := by ring
  rw [hden] at hB
  unfold fullGenerating regularGenerating zetaGlobalRegularCorrection
  dsimp [zetaGlobalRegularCorrection] at hB
  linear_combination (u : ℂ)*hA-(u : ℂ)*ratio y*hB+hp

theorem analyticAt_regularCorrection {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ zetaGlobalRegularCorrection s := by
  have hpsi := analyticOnNhd_digamma_re_pos (s/2) (by simpa using half_pos hs)
  unfold zetaGlobalRegularCorrection
  exact (((analyticAt_const.div analyticAt_id (Complex.ne_zero_of_re_pos hs)).sub
    analyticAt_const).add ((hpsi.comp (f := fun z : ℂ => z/2)
      (analyticAt_id.div_const)).div_const))

theorem analyticAt_xi_logDeriv {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (logDeriv riemannXi) s := by
  have hxi := analyticOnNhd_riemannXi s (mem_univ s)
  have hn : riemannXi s ≠ 0 := by
    intro hz
    have h := (riemannXi_eq_zero_iff_isNontrivialZetaZero s).mp hz
    linarith [NontrivialZetaZero.re_lt_one ⟨s, h⟩]
  exact hxi.deriv.div hxi hn

/-- The complete correction is regular on a fixed disk larger than the
selected source radius. This includes the whole shifted xi term. -/
theorem analyticOnNhd_regularGenerating {u y : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 10001/20000) (hy : 54 < |y|) :
    AnalyticOnNhd ℂ (regularGenerating u y) (Metric.closedBall 0 2) := by
  intro t ht
  have ht' : ‖t‖ ≤ 2 := by simpa using ht
  have hA := (analyticAt_regularCorrection (original_re_pos hu0 hu ht')).comp
    (f := fun t : ℂ => center y-(u : ℂ)*t)
    (show AnalyticAt ℂ (fun t : ℂ => center y-(u : ℂ)*t) t from
      analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
  have hB := (analyticAt_regularCorrection
    (lt_trans (by norm_num) (shifted_re_gt_one hu0 hu hy ht'))).comp
      (f := fun t : ℂ => center y+1-(u : ℂ)*ratio y*t)
      (show AnalyticAt ℂ (fun t : ℂ => center y+1-(u : ℂ)*ratio y*t) t from
        analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
  have hX := (analyticAt_xi_logDeriv (shifted_re_gt_one hu0 hu hy ht')).comp
    (f := fun t : ℂ => center y+1-(u : ℂ)*ratio y*t)
    (show AnalyticAt ℂ (fun t : ℂ => center y+1-(u : ℂ)*ratio y*t) t from
      analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
  exact ((analyticAt_const.mul hA).sub (analyticAt_const.mul hB)).add
    (analyticAt_const.mul hX)

/-- A geometric Cauchy estimate for the entire regular correction,
including the shifted full xi response. -/
theorem regular_coefficient_bound {u y : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 10001/20000) (hy : 54 < |y|) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      ‖signedTaylorMoment n (regularGenerating u y) 0‖ ≤ M*(2/3 : ℝ)^n := by
  have ha := (analyticOnNhd_regularGenerating hu0 hu hy).mono
    (Metric.closedBall_subset_closedBall (by norm_num : (3/2 : ℝ) ≤ 2))
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) (3/2 : ℝ)).image_of_continuousOn
    ha.continuousOn).isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM _ ⟨0, Metric.mem_closedBall_self (by norm_num), rfl⟩)
  refine ⟨M, hM0, fun n => ?_⟩
  have hd : DiffContOnCl ℂ (regularGenerating u y) (Metric.ball 0 (3/2 : ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (3/2 : ℝ) ≠ 0)]
    exact ha.differentiableOn
  have h := norm_signedTaylorMoment_le (by norm_num : (0 : ℝ) < 3/2) hd
    (fun z hz => hM _ ⟨z, Metric.sphere_subset_closedBall hz, rfl⟩) n
  rw [div_eq_mul_inv, ← inv_pow] at h
  norm_num only [inv_div] at h
  exact h

/-- Under the adaptive upper-order restriction, the exact arithmetic
correction has a fixed power saving in the prime. This is pointwise;
no source-normalized packet estimate is implicit. -/
theorem multiplier_error_le {y : ℝ} (hy : 54 < |y|) (k p : ℕ)
    (hp : 1 ≤ p) (hk : (k : ℝ) ≤ 4*Real.log p) :
    ‖ratio y^k/(p : ℂ)‖ ≤ Real.exp (-(99/100 : ℝ)*Real.log p) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have hC : ‖ratio y‖ ≤ Real.exp (1/1000) := by
    have he := Real.add_one_le_exp (1/1000 : ℝ)
    linarith [norm_ratio_lt hy]
  rw [norm_div, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ Real.exp (1/1000)^k/(p : ℝ) := by gcongr
    _ = Real.exp ((k : ℝ)/1000-Real.log p) := by
      rw [← Real.exp_nat_mul, Real.exp_sub, Real.exp_log hpR]
      congr 2
      ring
    _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith

theorem analyticAt_zeta_logDeriv {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (fun z => -logDeriv riemannZeta z) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hz := analyticOn_riemannZeta s (by simpa using hs1)
  exact (hz.deriv.div hz (riemannZeta_ne_zero_of_one_lt_re hs)).neg

/-- Taylor's theorem at a safe center, with the factorial and alternating
sign convention used by the repository. -/
theorem hasSum_scaled_moments {f : ℂ → ℂ} {s a t : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball s r)) (ht : ‖a*t‖ < r) :
    HasSum (fun n : ℕ => a^n*t^n*signedTaylorMoment n f s) (f (s-a*t)) := by
  have hm : s-a*t ∈ Metric.ball s r := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg] using ht
  have h := Complex.hasSum_taylorSeries_on_ball hf hm
  apply h.congr_fun
  intro n
  rw [show s-a*t-s = (-1)*a*t by ring, mul_pow, mul_pow]
  simp only [signedTaylorMoment, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The full von Mangoldt generating series is derived from its actual
Taylor moments on an initial regular disk, before meromorphic continuation. -/
theorem hasSum_fullGenerating {u y : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 10001/20000) (hy : 54 < |y|) {t : ℂ} (ht : ‖t‖ < 1/4) :
    HasSum (fun n : ℕ => fullLeg u y n*t^n) (fullGenerating u y t) := by
  have hd (s : ℂ) (hs : (3/2 : ℝ) ≤ s.re) :
      DifferentiableOn ℂ (fun z => -logDeriv riemannZeta z) (Metric.ball s (1/2)) := by
    intro z hz
    have hz' : ‖z-s‖ < 1/2 := mem_ball_iff_norm.mp hz
    have hre := Complex.abs_re_le_norm (z-s)
    have h1 : 1 < z.re := by
      simp only [Complex.sub_re] at hre
      have := neg_le_abs (z.re-s.re)
      linarith
    exact (analyticAt_zeta_logDeriv h1).differentiableAt.differentiableWithinAt
  have hA : ‖(u : ℂ)*t‖ < 1/2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
    nlinarith [norm_nonneg t]
  have hB : ‖((u : ℂ)*ratio y)*t‖ < 1/2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
    have hprod : u*‖ratio y‖ ≤ (10001/20000 : ℝ)*(1001/1000) := by
      gcongr
      exact (norm_ratio_lt hy).le
    nlinarith [norm_nonneg t, mul_nonneg hu0 (norm_nonneg (ratio y))]
  have h := ((hasSum_scaled_moments (hd (center y) (by norm_num [center])) hA).mul_left
    (u : ℂ)).sub
      ((hasSum_scaled_moments (hd (center y+1) (by norm_num [center])) hB).mul_left
        ((u : ℂ)*ratio y))
  change HasSum _ (fullGenerating u y t) at h
  apply h.congr_fun
  intro n
  simp only [fullLeg, zetaPrimeLogMoment, pow_succ, mul_pow]
  ring

end
end RiemannGaussian.ZetaRieszShiftedCenter
