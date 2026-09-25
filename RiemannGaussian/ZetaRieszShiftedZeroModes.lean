/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszShiftedCenter
import RiemannGaussian.RiemannXiGlobalLogDerivative
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Genuine global zero coefficients

The paired global xi identity is differentiated using locally uniform
convergence with a multiplicity-weighted inverse-square majorant. All
resulting zero terms have their actual multiplicities. No reflected modes
or hard-share transfer occurs here.
-/

namespace RiemannGaussian.ZetaRieszShiftedCenter
noncomputable section
open Complex Filter Metric Set Topology
open scoped BigOperators Classical

private theorem hasSum_iteratedDeriv_of_majorant {ι : Type*}
    {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U) {b : ι → ℝ} (hb : Summable b)
    (hbound : ∀ i z, z ∈ U → ‖F i z‖ ≤ b i) {s : ℂ} (hs : s ∈ U) (n : ℕ) :
    HasSum (fun i => iteratedDeriv n (F i) s)
      (iteratedDeriv n (fun z => ∑' i, F i z) s) := by
  have hbase := (tendstoUniformlyOn_tsum hb hbound).tendstoLocallyUniformlyOn
  have hdiff (n : ℕ) : TendstoLocallyUniformlyOn
      (fun S : Finset ι => iteratedDeriv n (fun z => ∑ i ∈ S, F i z))
      (iteratedDeriv n (fun z => ∑' i, F i z)) atTop U := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hbase
    | succ n ih =>
      simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv
        (Eventually.of_forall (fun S z hz => by
          simpa only [iteratedDeriv_eq_iterate, Finset.sum_apply] using
            ((Finset.analyticAt_fun_sum S (fun i _ => hF i z hz)).iterated_deriv n).differentiableAt.differentiableWithinAt (s := U))) hU
  change Tendsto (fun S : Finset ι => ∑ i ∈ S, iteratedDeriv n (F i) s) atTop _
  convert (hdiff n).tendsto_at hs using 1
  ext S
  exact (iteratedDeriv_fun_sum (fun i _ => (hF i s hs).contDiffAt)).symm

theorem center_zero_distance (y : ℝ) (rho : NontrivialZetaZero) :
    1/2 < ‖center y-rho.1‖ := by
  have hr := NontrivialZetaZero.re_lt_one rho
  have hn := Complex.re_le_norm (center y-rho.1)
  have hc : (center y).re = 3/2 := by simp [center]
  rw [Complex.sub_re, hc] at hn
  linarith

/-- The given global inverse-square theorem also controls distances from
the actual evaluation center. -/
theorem summable_center_inverse_square (y : ℝ) :
    Summable (fun rho : NontrivialZetaZero =>
      (analyticZetaZeroMultiplicity rho : ℝ)/‖center y-rho.1‖^2) := by
  let K : ℝ := 6+8*‖center y‖^2
  apply (summable_distinct_zetaZeroInverseSquareNorm.mul_left K).of_nonneg_of_le
    (fun rho => by positivity)
  intro rho
  have hd := center_zero_distance y rho
  have ht : ‖(rho.1 : ℂ)‖ ≤ ‖center y‖+‖center y-rho.1‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le (center y) (center y-rho.1)
  have ht2 := mul_self_le_mul_self (norm_nonneg _) ht
  have hw : 1+‖(rho.1 : ℂ)‖^2 ≤ K*‖center y-rho.1‖^2 := by
    dsimp [K]
    have hs : 1 ≤ 4*‖center y-rho.1‖^2 := by nlinarith
    have hss := mul_le_mul_of_nonneg_left hs (sq_nonneg ‖center y‖)
    nlinarith [sq_nonneg (‖center y‖-‖center y-rho.1‖)]
  calc
    _ ≤ (analyticZetaZeroMultiplicity rho : ℝ)*
        (K/(1+‖(rho.1 : ℂ)‖^2)) := by
      rw [div_eq_mul_inv]
      gcongr
      rw [← one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      simpa only [one_mul] using hw
    _ = _ := by ring

private theorem near_center_re (y : ℝ) {z : ℂ}
    (hz : z ∈ ball (center y) (1/4 : ℝ)) : 1 < z.re := by
  have hn := mem_ball_iff_norm.mp hz
  have hr := Complex.abs_re_le_norm (z-center y)
  have hc : (center y).re = 3/2 := by simp [center]
  rw [Complex.sub_re, hc] at hr
  have := neg_le_abs (z.re-3/2)
  linarith

private theorem analytic_difference (y : ℝ) (rho : NontrivialZetaZero) :
    AnalyticOnNhd ℂ (fun z => zetaLogDerivDifferenceSummand z (center y) rho)
      (ball (center y) (1/4 : ℝ)) := by
  intro z hz
  have hn : z-rho.1 ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    have := near_center_re y hz
    have := NontrivialZetaZero.re_lt_one rho
    simp only [Complex.sub_re]
    linarith
  exact analyticAt_const.mul ((analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    hn).sub analyticAt_const)

private theorem difference_majorant (y : ℝ) (rho : NontrivialZetaZero) {z : ℂ}
    (hz : z ∈ ball (center y) (1/4 : ℝ)) :
    ‖zetaLogDerivDifferenceSummand z (center y) rho‖ ≤
      (analyticZetaZeroMultiplicity rho : ℝ)/‖center y-rho.1‖^2 := by
  have hd := center_zero_distance y rho
  have hn := mem_ball_iff_norm.mp hz
  have htri : ‖center y-rho.1‖ ≤ ‖z-center y‖+‖z-rho.1‖ := by
    simpa only [sub_sub_sub_cancel_right, norm_sub_rev (center y) z, norm_sub_rev rho.1 z] using
      norm_sub_le (center y-z) (rho.1-z)
  have hhalf : ‖center y-rho.1‖/2 ≤ ‖z-rho.1‖ := by linarith
  have hdz : z-rho.1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hdc : center y-rho.1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : 1/(z-rho.1)-1/(center y-rho.1) =
      (center y-z)/((z-rho.1)*(center y-rho.1)) := by field_simp; ring
  have hq : ‖center y-z‖/(‖z-rho.1‖*‖center y-rho.1‖) ≤
      1/‖center y-rho.1‖^2 := by
    rw [norm_sub_rev (center y) z]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hhalf (norm_nonneg (center y-rho.1))
    nlinarith
  rw [zetaLogDerivDifferenceSummand, he, norm_mul, norm_div, norm_mul,
    Complex.norm_natCast]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hq
    (Nat.cast_nonneg (analyticZetaZeroMultiplicity rho))

private theorem signedMoment_reciprocal (s a : ℂ) (n : ℕ) :
    signedTaylorMoment n (fun z => 1/(z-a)) s = ((s-a)⁻¹)^(n+1) := by
  have ht := congrFun (iteratedDeriv_comp_const_add n (fun z : ℂ => (z-a)⁻¹) s) 0
  simp only [add_zero] at ht
  rw [show (fun z : ℂ => 1/(z-a)) = (fun z => (z-a)⁻¹) by ext; simp, signedTaylorMoment, ← ht]
  have he : (fun z : ℂ => (s+z-a)⁻¹) = (fun z => (1*z+(s-a))⁻¹) := by
    ext z; congr 1; ring
  rw [he]
  simpa only [signedTaylorMoment, one_pow, one_mul] using signedTaylorMoment_inv_linear n 1 (s-a)

/-- Every nonconstant coefficient of the global xi logarithmic derivative
is an absolutely summable genuine-zero power sum. -/
theorem hasSum_global_zero_moment (y : ℝ) (n : ℕ) (hn : 0 < n) :
    HasSum (fun rho : NontrivialZetaZero => (analyticZetaZeroMultiplicity rho : ℂ)*
      ((center y-rho.1)⁻¹)^(n+1)) (signedTaylorMoment n (logDeriv riemannXi) (center y)) := by
  have h := (hasSum_iteratedDeriv_of_majorant isOpen_ball (analytic_difference y)
    (summable_center_inverse_square y) (fun rho z hz => difference_majorant y rho hz)
    (mem_ball_self (by norm_num : (0 : ℝ) < 1/4)) n).mul_left
      ((-1 : ℂ)^n/(n.factorial : ℂ))
  have hxi : riemannXi (center y) ≠ 0 := by
    intro hz
    have hzero := (riemannXi_eq_zero_iff_isNontrivialZetaZero (center y)).mp hz
    have := NontrivialZetaZero.re_lt_one ⟨center y, hzero⟩
    norm_num [center] at this
  have he : (fun z => ∑' rho, zetaLogDerivDifferenceSummand z (center y) rho) =ᶠ[𝓝 (center y)]
      (fun z => logDeriv riemannXi z-logDeriv riemannXi (center y)) := by
    filter_upwards [ball_mem_nhds (center y) (by norm_num : (0 : ℝ) < 1/4)] with z hz
    have hzn : riemannXi z ≠ 0 := by
      intro hzero
      have hzero' := (riemannXi_eq_zero_iff_isNontrivialZetaZero z).mp hzero
      have := NontrivialZetaZero.re_lt_one ⟨z, hzero'⟩
      linarith [near_center_re y hz]
    exact tsum_zetaLogDerivDifference hzn hxi
  change HasSum _ (signedTaylorMoment n _ (center y)) at h
  rw [signedTaylorMoment_congr n he, signedTaylorMoment_sub n
    (analyticAt_xi_logDeriv (by norm_num [center])) analyticAt_const] at h
  have hc (c : ℂ) : signedTaylorMoment n (fun _ : ℂ => c) (center y) = 0 := by
    simp [signedTaylorMoment, iteratedDeriv_const, hn.ne']
  rw [hc, sub_zero] at h
  apply h.congr_fun
  intro rho
  symm
  change signedTaylorMoment n (fun z => (analyticZetaZeroMultiplicity rho : ℂ)*
    (1/(z-rho.1)-1/(center y-rho.1))) (center y) = _
  rw [signedTaylorMoment_const_mul,
    signedTaylorMoment_sub n ?_ analyticAt_const, hc, sub_zero, signedMoment_reciprocal]
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    (norm_pos_iff.mp (lt_trans (by norm_num) (center_zero_distance y rho)))

/-- Actual Taylor coefficient, without the alternating-moment convention. -/
def coefficient (n : ℕ) (f : ℂ → ℂ) : ℂ :=
  (-1 : ℂ)^n*signedTaylorMoment n f 0

private theorem iteratedDeriv_scale (f : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t => f (a*t)) = fun t => a^n*iteratedDeriv n f (a*t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul, iteratedDeriv_succ,
      pow_succ]
    ring

theorem coefficient_affine (f : ℂ → ℂ) (s a b : ℂ) (n : ℕ) :
    coefficient n (fun t => a*f (s-b*t)) = a*b^n*signedTaylorMoment n f s := by
  have hh : (fun t => f (s-b*t)) = (fun t => (fun z => f (s+z)) ((-b)*t)) := by
    ext t; congr 1; ring
  rw [coefficient, signedTaylorMoment_const_mul]
  rw [hh, signedTaylorMoment,
    iteratedDeriv_scale (fun z => f (s+z)) (-b) n]
  simp only [mul_zero, iteratedDeriv_comp_const_add, add_zero]
  rw [show -b = (-1)*b by ring, mul_pow]
  have hn : (-1 : ℂ)^n*(-1)^n = 1 := by rw [← mul_pow]; simp
  unfold signedTaylorMoment
  calc
    _ = a*b^n*((-1 : ℂ)^n/(n.factorial : ℂ)*iteratedDeriv n f s)*
        ((-1 : ℂ)^n*(-1)^n) := by ring
    _ = _ := by rw [hn, mul_one]

theorem coefficient_sub (n : ℕ) {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    coefficient n (fun t => f t-g t) = coefficient n f-coefficient n g := by
  simp only [coefficient, signedTaylorMoment_sub n hf hg, mul_sub]

theorem coefficient_fullGenerating (u y : ℝ) (n : ℕ) :
    coefficient n (fullGenerating u y) = fullLeg u y n := by
  have hA : AnalyticAt ℂ (fun t : ℂ => (u : ℂ)*
      (-logDeriv riemannZeta (center y-u*t))) 0 := by
    apply analyticAt_const.mul
    apply AnalyticAt.comp (g := fun z => -logDeriv riemannZeta z)
      (f := fun t : ℂ => center y-u*t) ?_
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    simpa using analyticAt_zeta_logDeriv (s := center y) (by norm_num [center])
  have hB : AnalyticAt ℂ (fun t : ℂ => (u : ℂ)*ratio y*
      (-logDeriv riemannZeta (center y+1-u*ratio y*t))) 0 := by
    apply analyticAt_const.mul
    apply AnalyticAt.comp (g := fun z => -logDeriv riemannZeta z)
      (f := fun t : ℂ => center y+1-u*ratio y*t) ?_
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    simpa using analyticAt_zeta_logDeriv (s := center y+1) (by norm_num [center])
  unfold fullGenerating
  rw [coefficient_sub n hA hB,
    coefficient_affine (fun z => -logDeriv riemannZeta z) (center y) u u n,
    coefficient_affine (fun z => -logDeriv riemannZeta z) (center y+1)
      ((u : ℂ)*ratio y) ((u : ℂ)*ratio y) n]
  simp only [fullLeg, zetaPrimeLogMoment, pow_succ, mul_pow]
  ring

/-- Every genuine global zero contributes negatively, with its full
analytic multiplicity. This is a coefficient identity, not a masked limit. -/
theorem hasSum_negative_global_coefficient (u y : ℝ) (n : ℕ) (hn : 0 < n) :
    HasSum (fun rho : NontrivialZetaZero => -(analyticZetaZeroMultiplicity rho : ℂ)*
      ((u : ℂ)/(center y-rho.1))^(n+1))
      (coefficient n (fun t => -(u : ℂ)*logDeriv riemannXi (center y-u*t))) := by
  rw [coefficient_affine]
  have h := (hasSum_global_zero_moment y n hn).mul_left (-(u : ℂ)*(u : ℂ)^n)
  apply h.congr_fun
  intro rho
  simp only [div_eq_mul_inv, mul_pow, pow_succ]
  ring

theorem coefficient_add (n : ℕ) {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    coefficient n (fun t => f t+g t) = coefficient n f+coefficient n g := by
  simp only [coefficient, signedTaylorMoment_add n hf hg, mul_add]

theorem fullLeg_eq_global_zeros {u y : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 10001/20000) (hy : 54 < |y|) (n : ℕ) (hn : 0 < n) :
    fullLeg u y n =
      (∑' rho : NontrivialZetaZero, -(analyticZetaZeroMultiplicity rho : ℂ)*
        ((u : ℂ)/(center y-rho.1))^(n+1))+
      coefficient n (regularGenerating u y) := by
  have he : fullGenerating u y =ᶠ[𝓝 (0 : ℂ)]
      (fun t => -(u : ℂ)*logDeriv riemannXi (center y-u*t)+regularGenerating u y t) := by
    have hc : ContinuousAt (fun t : ℂ => (center y-u*t).re) 0 := by fun_prop
    have hr : ∀ᶠ t : ℂ in 𝓝 0, 1 < (center y-u*t).re :=
      hc (lt_mem_nhds (by norm_num [center]))
    filter_upwards [hr, ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 2)] with t ht hball
    apply global_decomposition hu0 hu hy (by simpa using (mem_ball.mp hball).le)
    · intro h; rw [h] at ht; norm_num at ht
    · exact riemannZeta_ne_zero_of_one_lt_re ht
  have hX : AnalyticAt ℂ (fun t : ℂ => -(u : ℂ)*logDeriv riemannXi (center y-u*t)) 0 := by
    apply analyticAt_const.mul
    apply AnalyticAt.comp (g := logDeriv riemannXi)
      (f := fun t : ℂ => center y-u*t) ?_
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    simpa using analyticAt_xi_logDeriv (s := center y) (by norm_num [center])
  rw [← coefficient_fullGenerating, coefficient, signedTaylorMoment_congr n he,
    ← coefficient, coefficient_add n hX
      (analyticOnNhd_regularGenerating hu0 hu hy 0 (mem_closedBall_self (by norm_num))),
    ← (hasSum_negative_global_coefficient u y n hn).tsum_eq]

/-- Global negative residues plus a geometrically small analytic error.
This is uniform in the order, for the fixed evaluation ordinate. -/
theorem fullLeg_global_error_bound {u y : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 10001/20000) (hy : 54 < |y|) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, 0 < n →
      ‖fullLeg u y n-(∑' rho : NontrivialZetaZero,
        -(analyticZetaZeroMultiplicity rho : ℂ)*((u : ℂ)/(center y-rho.1))^(n+1))‖ ≤
          M*(2/3 : ℝ)^n := by
  obtain ⟨M, hM, hb⟩ := regular_coefficient_bound hu0 hu hy
  refine ⟨M, hM, fun n hn => ?_⟩
  rw [fullLeg_eq_global_zeros hu0 hu hy n hn, add_sub_cancel_left]
  simpa only [coefficient, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul] using hb n

end
end RiemannGaussian.ZetaRieszShiftedCenter
