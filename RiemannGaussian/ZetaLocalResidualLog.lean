import RiemannGaussian.ZetaLocalResidualBounds
import RiemannGaussian.EtaLogarithmicStrip
import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# Logarithmic derivative control after complete local zero removal

A normalized analytic logarithm retains the complete local residual.
The actual eta upper bound and Möbius center floor bound its real part.
Borel--Carathéodory and Cauchy's estimate give an explicit logarithmic
bound for the residual derivative on the inner half-disc.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The logarithmic height appropriate to the translated unit disc. -/
def localZetaLogHeight (y : ℝ) : ℝ := Real.log (|y| + 22)

/-- The local logarithmic height exceeds two at every real ordinate. -/
theorem two_lt_localZetaLogHeight (y : ℝ) : 2 < localZetaLogHeight y :=
  (two_lt_etaLogHeight y).trans_le (Real.log_le_log (by positivity) (by linarith))

/-- The zero-free local residual has a normalized logarithmic primitive. -/
theorem exists_localZetaCanonicalLog (y : ℝ) : ∃ L : ℂ → ℂ, L 0 = 0 ∧
    ∀ z ∈ ball 0 (localZetaCanonicalRadius y), HasDerivAt L (logDeriv (localZetaCanonicalResidual y) z) z := by
  have hd : DifferentiableOn ℂ (logDeriv (localZetaCanonicalResidual y))
      (ball 0 (localZetaCanonicalRadius y)) := by
    intro z hz
    have hg := (localZetaCanonicalResidual_decomp y).analyticOnNhd z (ball_subset_closedBall hz)
    have hl : AnalyticAt ℂ (logDeriv (localZetaCanonicalResidual y)) z := by
      simpa only [logDeriv] using hg.deriv.div hg
        ((localZetaCanonicalResidual_decomp y).ne_zero z (ball_subset_closedBall hz))
    exact hl.differentiableAt.differentiableWithinAt
  exact hd.isExactOn_ball.with_val_at 0 0

/-- The chosen logarithm is normalized at the actual safe center. -/
def localZetaCanonicalLog (y : ℝ) : ℂ → ℂ := Classical.choose (exists_localZetaCanonicalLog y)

/-- The normalized logarithm vanishes at the disc center. -/
@[simp] theorem localZetaCanonicalLog_zero (y : ℝ) : localZetaCanonicalLog y 0 = 0 :=
  (Classical.choose_spec (exists_localZetaCanonicalLog y)).1

/-- Its derivative is the actual local residual logarithmic derivative. -/
theorem localZetaCanonicalLog_hasDerivAt (y : ℝ) {z : ℂ}
    (hz : z ∈ ball 0 (localZetaCanonicalRadius y)) :
    HasDerivAt (localZetaCanonicalLog y) (logDeriv (localZetaCanonicalResidual y) z) z :=
  (Classical.choose_spec (exists_localZetaCanonicalLog y)).2 z hz

/-- Exponentiating the normalized logarithm recovers the whole local
residual, with its true center value retained. -/
theorem exp_localZetaCanonicalLog_mul_zero_eq (y : ℝ) {z : ℂ}
    (hz : z ∈ ball 0 (localZetaCanonicalRadius y)) :
    Complex.exp (localZetaCanonicalLog y z) * localZetaCanonicalResidual y 0 = localZetaCanonicalResidual y z := by
  let R := localZetaCanonicalRadius y
  let g := localZetaCanonicalResidual y
  let L := localZetaCanonicalLog y
  let q : ℂ → ℂ := (fun w ↦ Complex.exp (-L w)) * g
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self (localZetaCanonicalRadius_pos y)
  have hdiff : DifferentiableOn ℂ q (ball 0 R) := by
    intro w hw
    have hL := localZetaCanonicalLog_hasDerivAt y hw
    have hg := (localZetaCanonicalResidual_decomp y).analyticOnNhd w (ball_subset_closedBall hw)
    exact (hL.neg.cexp.mul hg.differentiableAt.hasDerivAt).differentiableAt.differentiableWithinAt
  have hderiv : EqOn (deriv q) 0 (ball 0 R) := by
    intro w hw
    have hL := localZetaCanonicalLog_hasDerivAt y hw
    have hg := (localZetaCanonicalResidual_decomp y).analyticOnNhd w (ball_subset_closedBall hw)
    have hq : HasDerivAt q
        (Complex.exp (-L w) * (-logDeriv g w) * g w + Complex.exp (-L w) * deriv g w) w :=
      hL.neg.cexp.mul hg.differentiableAt.hasDerivAt
    rw [hq.deriv]
    change Complex.exp (-L w) * (-logDeriv g w) * g w + Complex.exp (-L w) * deriv g w = 0
    rw [logDeriv_apply, mul_assoc (Complex.exp (-L w)) (-(deriv g w / g w)) (g w),
      neg_mul, div_mul_cancel₀ _ ((localZetaCanonicalResidual_decomp y).ne_zero w (ball_subset_closedBall hw))]
    ring
  have he := isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball hdiff hderiv hzero hz
  have hg0 : g 0 = Complex.exp (-L z) * g z := by
    simpa [q, L, localZetaCanonicalLog_zero] using he
  change Complex.exp (L z) * g 0 = g z
  rw [hg0, ← mul_assoc, ← Complex.exp_add]
  simp

/-- The actual upper envelope and center floor give a logarithmic
bound for the real part of the complete residual logarithm. -/
theorem localZetaCanonicalLog_re_le (y : ℝ) {z : ℂ}
    (hz : z ∈ ball 0 (localZetaCanonicalRadius y)) :
    (localZetaCanonicalLog y z).re ≤ 4 * localZetaLogHeight y := by
  have he := congrArg norm (exp_localZetaCanonicalLog_mul_zero_eq y hz)
  rw [norm_mul, Complex.norm_exp] at he
  have hlow := sixteenth_le_norm_localZetaCanonicalResidual_zero y
  have hu := norm_localZetaCanonicalResidual_le y (ball_subset_closedBall hz)
  have hm := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (localZetaCanonicalLog y z).re).le
  have ht : 128 ≤ (|y| + 22) ^ 2 := by nlinarith [abs_nonneg y]
  have hp := mul_le_mul_of_nonneg_right ht (sq_nonneg (|y| + 22))
  have hexp : Real.exp (4 * localZetaLogHeight y) = (|y| + 22) ^ 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul,
      localZetaLogHeight, Real.exp_log (by positivity)]
  apply Real.exp_le_exp.mp
  rw [hexp]
  nlinarith

/-- The full complex logarithm obeys the Borel--Carathéodory bound
throughout the selected local disc. -/
theorem norm_localZetaCanonicalLog_le (y : ℝ) {z : ℂ}
    (hz : z ∈ ball 0 (localZetaCanonicalRadius y)) :
    ‖localZetaCanonicalLog y z‖ ≤
      8 * localZetaLogHeight y * ‖z‖ / (localZetaCanonicalRadius y - ‖z‖) := by
  have hd : DifferentiableOn ℂ (localZetaCanonicalLog y) (ball 0 (localZetaCanonicalRadius y)) :=
    fun _ hw ↦ (localZetaCanonicalLog_hasDerivAt y hw).differentiableAt.differentiableWithinAt
  have h := Complex.borelCaratheodory_zero
    (M := 4 * localZetaLogHeight y) (by linarith [two_lt_localZetaLogHeight y]) hd
    (fun _ hw ↦ localZetaCanonicalLog_re_le y hw) (localZetaCanonicalRadius_pos y) hz (localZetaCanonicalLog_zero y)
  convert h using 1
  ring

/-- Cauchy's estimate bounds the complete residual logarithmic
derivative on the half-disc by an explicit logarithmic height. -/
theorem norm_logDeriv_localZetaCanonicalResidual_le (y : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖logDeriv (localZetaCanonicalResidual y) z‖ ≤ 320 * localZetaLogHeight y := by
  have hR := (localZetaCanonicalRadius_spec y).1
  have hL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  have hbound {w : ℂ} (hw : w ∈ closedBall z (1 / 8 : ℝ)) : ‖w‖ ≤ 5 / 8 := by
    have hd : ‖w - z‖ ≤ 1 / 8 := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hn := norm_add_le (w - z) z
    rw [sub_add_cancel] at hn
    linarith
  have hsub : closedBall z (1 / 8 : ℝ) ⊆ ball 0 (localZetaCanonicalRadius y) := by
    intro w hw
    rw [mem_ball, dist_zero_right]
    linarith [hbound hw]
  have hd : DiffContOnCl ℂ (localZetaCanonicalLog y) (ball z (1 / 8 : ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (by norm_num : (1 / 8 : ℝ) ≠ 0)]
    intro w hw
    exact (localZetaCanonicalLog_hasDerivAt y (hsub hw)).differentiableAt.differentiableWithinAt
  have hsphere : ∀ w ∈ sphere z (1 / 8 : ℝ), ‖localZetaCanonicalLog y w‖ ≤ 40 * localZetaLogHeight y := by
    intro w hw
    have hnorm := hbound (sphere_subset_closedBall hw)
    have hden : 0 < localZetaCanonicalRadius y - ‖w‖ := by linarith
    apply (norm_localZetaCanonicalLog_le y (hsub (sphere_subset_closedBall hw))).trans
    rw [div_le_iff₀ hden]
    nlinarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 8) hd hsphere
  rw [(localZetaCanonicalLog_hasDerivAt y (by simpa using (show ‖z‖ < localZetaCanonicalRadius y by linarith))).deriv] at h
  convert h using 1
  ring

end

end RiemannGaussian
