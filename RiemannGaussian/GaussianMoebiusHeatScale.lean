import RiemannGaussian.GaussianMoebiusCancellation

/-!
# Gaussian Möbius cancellation at every positive heat time

The actual reciprocal contour estimate is made uniform in the arithmetic
center for each fixed positive heat time, including arbitrarily small times.
This retains the parameter needed to remove Gaussian smoothing at a finite
arithmetic cutoff. Both horizontal corrections and both infinite tails are
included in the envelope.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The fixed positive-time prefactor retains the full Gaussian normalization and all contour corrections. -/
def gaussianMoebiusHeatScalePrefactor (tau : ℝ) : ℝ :=
  gaussianMoebiusContourConstant * (3 + 4000000 * Real.sqrt (2 * Real.pi / tau)) *
    Real.exp (2 * tau) / Real.sqrt (Real.pi / tau)

/-- The actual heat-scale prefactor is strictly positive at every positive heat time. -/
theorem gaussianMoebiusHeatScalePrefactor_pos {tau : ℝ} (htau : 0 < tau) :
    0 < gaussianMoebiusHeatScalePrefactor tau := by
  have hC := sixteen_le_gaussianMoebiusContourConstant
  unfold gaussianMoebiusHeatScalePrefactor
  positivity

/-- At every positive heat time, the complete actual contour bound fits the saved left-line scale beyond explicit scale conditions. -/
theorem gaussianMoebiusSum_le_heatScale_prefactor {a tau : ℝ} (htau : 0 < tau)
    (ha : 22 ≤ a) (hheat : 1 ≤ tau * a)
    (hlarge : Real.exp (1 / (500000 * zetaReciprocalLowHeightWidth)) ≤ a) :
    |gaussianMoebiusSum a tau| ≤ gaussianMoebiusHeatScalePrefactor tau * a *
      Real.exp (33000000 * localZetaLogHeight a ^ 2) *
        Real.exp (a * (1 - zetaReciprocalContourWidth a)) := by
  let w := zetaReciprocalContourWidth a
  let B := zetaReciprocalContourBound a
  let D := moebiusDirichletMass (1 + w)
  let M := Real.exp (33000000 * localZetaLogHeight a ^ 2)
  let C := gaussianMoebiusContourConstant
  let X := Real.exp (a * (1 - w) + 2 * tau)
  have hw : 0 < w := zetaReciprocalContourWidth_pos a
  have hwle : w ≤ 1 / 8 := zetaReciprocalContourWidth_le_eighth a
  have hB : 0 < B := zetaReciprocalContourBound_pos a
  have hD : 0 ≤ D := le_trans zero_le_one (one_le_moebiusDirichletMass (by linarith))
  have hM : 1 ≤ M := Real.one_le_exp (by positivity)
  have hC : 16 ≤ C := sixteen_le_gaussianMoebiusContourConstant
  have hBC : B ≤ C * M := zetaReciprocalContourBound_le_logSquare a
  have hCM : 1 ≤ C * M := by nlinarith
  have hL : localZetaLogHeight a ≤ 2 * a := by
    have h := Real.log_le_sub_one_of_pos (show 0 < |a| + 22 by positivity)
    rw [abs_of_nonneg (by linarith)] at h
    change Real.log (|a| + 22) ≤ 2 * a
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hDle : D ≤ 4000000 * a :=
    (moebiusDirichletMass_contour_le_log (by linarith) hlarge).trans (by linarith)
  have hq : a ≤ tau * a ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ tau * a - 1 by linarith)]
  have hrealLeft : tau * (1 - w) ^ 2 ≤ 2 * tau := by
    nlinarith [mul_le_mul_of_nonneg_left (show (1 - w) ^ 2 ≤ 2 by nlinarith) htau.le]
  have hrealRight : tau * (1 + w) ^ 2 ≤ 2 * tau := by
    nlinarith [mul_le_mul_of_nonneg_left (show (1 + w) ^ 2 ≤ 2 by nlinarith) htau.le]
  have haw : 2 * a * w ≤ a / 4 := by
    nlinarith [mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1 / 8 - w by linarith)]
  have hleft : Real.exp (a * (1 - w) + tau * (1 - w) ^ 2) ≤ X := by
    apply Real.exp_le_exp.mpr
    linarith
  have htop : Real.exp (a * (1 + w) + tau * (1 + w) ^ 2 - tau * a ^ 2) ≤ X := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have htail : Real.exp (a * (1 + w) + tau * (1 + w) ^ 2 - tau * a ^ 2 / 2) ≤ X := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hb := gaussianMoebiusSum_contour_bound (a := a) (tau := tau) (T := a)
    (by linarith) htau (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hleft (show 0 ≤ 2 * a * B by positivity)
  have h2 := mul_le_mul_of_nonneg_left htop (show 0 ≤ 4 * w * B by positivity)
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail hD)
    (Real.sqrt_nonneg (2 * Real.pi / tau))
  have hcoef : 2 * a * B + 4 * w * B + D * Real.sqrt (2 * Real.pi / tau) ≤
      C * (3 + 4000000 * Real.sqrt (2 * Real.pi / tau)) * a * M := by
    calc
      _ ≤ 3 * a * B + (4000000 * a * Real.sqrt (2 * Real.pi / tau)) * (C * M) := by
        apply add_le_add
        · have h := mul_le_mul_of_nonneg_right (show 2 * a + 4 * w ≤ 3 * a by linarith) hB.le
          nlinarith
        · exact (mul_le_mul_of_nonneg_right hDle (Real.sqrt_nonneg _)).trans
            (le_mul_of_one_le_right (by positivity) hCM)
      _ ≤ 3 * a * (C * M) + (4000000 * a * Real.sqrt (2 * Real.pi / tau)) * (C * M) := by gcongr
      _ = _ := by ring
  apply hb.trans
  calc
    _ ≤ ((2 * a * B + 4 * w * B + D * Real.sqrt (2 * Real.pi / tau)) * X) /
        Real.sqrt (Real.pi / tau) := by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      dsimp only [w, B, D] at h1 h2 h3
      nlinarith
    _ ≤ (C * (3 + 4000000 * Real.sqrt (2 * Real.pi / tau)) * a * M * X) /
        Real.sqrt (Real.pi / tau) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
        (Real.sqrt_nonneg _)
    _ = _ := by
      dsimp [X, C, M, w, gaussianMoebiusHeatScalePrefactor]
      rw [Real.exp_add]
      ring

/-- The fixed logarithmic cost at a specified heat time. -/
def gaussianMoebiusHeatScaleExponent (tau : ℝ) : ℝ :=
  33000001 + |Real.log (gaussianMoebiusHeatScalePrefactor tau)|

/-- The complete positive-time arithmetic bound has a fixed squared-logarithm cost above its saved exponent. -/
theorem gaussianMoebiusSum_le_heatScale_logSquare {a tau : ℝ} (htau : 0 < tau)
    (ha : 22 ≤ a) (hheat : 1 ≤ tau * a)
    (hlarge : Real.exp (1 / (500000 * zetaReciprocalLowHeightWidth)) ≤ a) :
    |gaussianMoebiusSum a tau| ≤ Real.exp
      (a - a / (500000 * localZetaLogHeight a) + gaussianMoebiusHeatScaleExponent tau * localZetaLogHeight a ^ 2) := by
  let L := localZetaLogHeight a
  have hL : 2 < L := two_lt_localZetaLogHeight a
  have hP := gaussianMoebiusHeatScalePrefactor_pos htau
  have haexp : a ≤ Real.exp L := by
    rw [show Real.exp L = |a| + 22 by exact Real.exp_log (by positivity)]
    exact (le_abs_self a).trans (by linarith)
  have hexponent : Real.log (gaussianMoebiusHeatScalePrefactor tau) + L + 33000000 * L ^ 2 ≤
      gaussianMoebiusHeatScaleExponent tau * L ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ L ^ 2 by nlinarith)
      (abs_nonneg (Real.log (gaussianMoebiusHeatScalePrefactor tau)))
    unfold gaussianMoebiusHeatScaleExponent
    nlinarith [le_abs_self (Real.log (gaussianMoebiusHeatScalePrefactor tau)), sq_nonneg (L - 2)]
  have hpre : gaussianMoebiusHeatScalePrefactor tau * a * Real.exp (33000000 * L ^ 2) ≤
      Real.exp (gaussianMoebiusHeatScaleExponent tau * L ^ 2) := by
    calc
      _ ≤ gaussianMoebiusHeatScalePrefactor tau * Real.exp L * Real.exp (33000000 * L ^ 2) := by gcongr
      _ = Real.exp (Real.log (gaussianMoebiusHeatScalePrefactor tau) + L + 33000000 * L ^ 2) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hP]
      _ ≤ _ := Real.exp_le_exp.mpr hexponent
  apply (gaussianMoebiusSum_le_heatScale_prefactor htau ha hheat hlarge).trans
  apply (mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add, zetaReciprocalContourWidth_eq_stripWidth (by linarith) hlarge, zetaReciprocalStripWidth]
  congr 1
  dsimp [L]
  ring

/-- Every fixed positive heat time has the proved reciprocal-logarithm cancellation gain at all sufficiently large arithmetic centers. -/
theorem gaussianMoebiusSum_le_reciprocal_log_gain_eventually {tau : ℝ} (htau : 0 < tau) :
    ∀ᶠ a : ℝ in atTop, |gaussianMoebiusSum a tau| ≤
      Real.exp (a - a / (1000000 * localZetaLogHeight a)) := by
  have hzero : Tendsto (fun a : ℝ ↦
      (1000000 * gaussianMoebiusHeatScaleExponent tau) * (localZetaLogHeight a ^ 3 / a)) atTop (𝓝 0) := by
    simpa using (tendsto_localZetaLogHeight_pow_div_zero 3).const_mul
      (1000000 * gaussianMoebiusHeatScaleExponent tau)
  have hsmall := hzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop (22 : ℝ), eventually_ge_atTop (1 / tau),
    eventually_ge_atTop (Real.exp (1 / (500000 * zetaReciprocalLowHeightWidth)))] with a hc ha ht hl
  have hheat : 1 ≤ tau * a := by
    have h := (div_le_iff₀ htau).mp ht
    nlinarith
  have hL : 0 < localZetaLogHeight a := by linarith [two_lt_localZetaLogHeight a]
  rw [← mul_div_assoc, div_lt_iff₀ (by linarith : 0 < a)] at hc
  have hcost : gaussianMoebiusHeatScaleExponent tau * localZetaLogHeight a ^ 2 ≤
      a / (1000000 * localZetaLogHeight a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  apply (gaussianMoebiusSum_le_heatScale_logSquare htau ha hheat hl).trans
  apply Real.exp_le_exp.mpr
  have hhalf : a / (500000 * localZetaLogHeight a) = 2 * (a / (1000000 * localZetaLogHeight a)) := by ring
  linarith

/-- The actual signed Gaussian Möbius sum is o(exp(a)) at every fixed positive heat time. -/
theorem gaussianMoebiusSum_exp_ratio_tendsto_zero {tau : ℝ} (htau : 0 < tau) :
    Tendsto (fun a : ℝ ↦ gaussianMoebiusSum a tau / Real.exp a) atTop (𝓝 0) := by
  have hexp : Tendsto (fun a : ℝ ↦ Real.exp (-(a / (1000000 * localZetaLogHeight a)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_gaussianMoebiusReciprocalLogGain_atTop)
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [gaussianMoebiusSum_le_reciprocal_log_gain_eventually htau] with a ha
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos a)]
  apply (div_le_div_of_nonneg_right ha (Real.exp_pos a).le).trans_eq
  rw [← Real.exp_sub]
  congr 1
  ring

end

end RiemannGaussian
