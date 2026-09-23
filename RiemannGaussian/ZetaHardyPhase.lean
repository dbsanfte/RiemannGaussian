/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GammaContinuousPhase
import RiemannGaussian.RiemannXiSuzukiRealAxisCompletedLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Actual Hardy Z and a certified finite phase approximation

The estimated continuous Gamma phase gives the genuine real Hardy function
on the critical line. The finite 200-shift approximation preserves its sign
through height 22000. Thus finite sign computations can certify critical-line
zeros without a Gamma interval calculation or a numerical derivative.
Completeness of a zero list still requires a separate total count.
-/

namespace RiemannGaussian.ZetaHardyPhase
noncomputable section
open Complex Set

/-- The literal point on the critical line at height `T`. -/
def point (T : ℝ) : ℂ := 1 / 2 + T * I

/-- The positive real amplitude of the completed Gamma factor on the critical line. -/
def completedAmplitude (T : ℝ) : ℝ :=
  Real.exp (-Real.log Real.pi / 4) * GammaContinuousPhase.amplitude (1 / 4) (T / 2)

/-- The completed Gamma amplitude never vanishes. -/
theorem completedAmplitude_pos (T : ℝ) : 0 < completedAmplitude T :=
  mul_pos (Real.exp_pos _) (GammaContinuousPhase.amplitude_pos (by norm_num) _)

/-- The exact completed Gamma polar formula uses the continuously unwrapped theta. -/
theorem GammaR_eq_amplitude_mul_phase (T : ℝ) :
    Complex.Gammaℝ (point T) = (completedAmplitude T : ℂ) *
      Complex.exp (I * GammaPhaseApproximation.theta T) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : point T / 2 = ((1 / 4 : ℝ) : ℂ) + (T / 2 : ℝ) * I := by
    unfold point
    push_cast
    ring
  rw [Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hp, hs,
    GammaContinuousPhase.Gamma_eq_amplitude_mul_phase (by norm_num : (0 : ℝ) < 1 / 4)]
  have hl : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  rw [hl]
  have he : (Real.log Real.pi : ℂ) * (-point T / 2) =
      (-Real.log Real.pi / 4 : ℝ) + I * (-T / 2 * Real.log Real.pi : ℝ) := by
    unfold point
    push_cast
    ring
  rw [he, Complex.exp_add]
  have hphase : I * (-T / 2 * Real.log Real.pi : ℝ) +
      I * GammaPhaseApproximation.phase (1 / 4) (T / 2) =
      I * GammaPhaseApproximation.theta T := by
    unfold GammaPhaseApproximation.theta
    push_cast
    ring
  calc
    _ = (completedAmplitude T : ℂ) *
        (Complex.exp (I * (-T / 2 * Real.log Real.pi : ℝ)) *
          Complex.exp (I * GammaPhaseApproximation.phase (1 / 4) (T / 2))) := by
      simp only [completedAmplitude, Complex.ofReal_mul, Complex.ofReal_exp]
      ring
    _ = _ := by rw [← Complex.exp_add, hphase]

/-- The genuine Hardy function, using the full continuous theta phase. -/
def hardy (T : ℝ) : ℝ :=
  (Complex.exp (I * GammaPhaseApproximation.theta T) * riemannZeta (point T)).re

private theorem point_ne_one (T : ℝ) : point T ≠ 1 := by
  intro h
  have hh := congrArg Complex.re h
  norm_num [point] at hh

/-- The phase-rotated zeta value is exactly real at every critical-line point. -/
theorem rotated_zeta_im (T : ℝ) :
    (Complex.exp (I * GammaPhaseApproximation.theta T) * riemannZeta (point T)).im = 0 := by
  have hx := riemannXiSpectral_ofReal_im T
  have he : riemannXiSpectral (T : ℂ) = riemannXi (point T) := by
    unfold riemannXiSpectral completedSpectralCoordinate point
    congr 1
    ring
  have hpoly : point T * (1 - point T) = ((1 / 4 + T ^ 2 : ℝ) : ℂ) := by
    unfold point
    apply Complex.ext <;> simp [pow_two] <;> ring
  rw [he, riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos
    (by norm_num [point]) (point_ne_one T), hpoly, GammaR_eq_amplitude_mul_phase] at hx
  have hx' : (1 / 4 + T ^ 2) * completedAmplitude T *
      (Complex.exp (I * GammaPhaseApproximation.theta T) * riemannZeta (point T)).im = 0 := by
    simpa only [mul_assoc, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, add_zero, mul_add] using hx
  exact (mul_eq_zero.mp hx').resolve_left (by
    exact mul_ne_zero (by positivity) (completedAmplitude_pos T).ne')

/-- The complex phase-rotated value is the real Hardy function embedded in `ℂ`. -/
theorem hardy_ofReal (T : ℝ) :
    (hardy T : ℂ) = Complex.exp (I * GammaPhaseApproximation.theta T) * riemannZeta (point T) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using (rotated_zeta_im T).symm

/-- Hardy Z vanishes exactly at the actual critical-line zeta zeros. -/
theorem hardy_eq_zero_iff (T : ℝ) : hardy T = 0 ↔ riemannZeta (point T) = 0 := by
  rw [← Complex.ofReal_eq_zero, hardy_ofReal, mul_eq_zero]
  simp only [Complex.exp_ne_zero, false_or]

/-- The real Hardy function is continuous at every real height. -/
theorem continuous_hardy : Continuous hardy := by
  apply Complex.continuous_re.comp
  apply Continuous.mul
  · apply Complex.continuous_exp.comp
    apply continuous_const.mul
    apply Complex.continuous_ofReal.comp
    unfold GammaPhaseApproximation.theta
    apply Continuous.sub
    · exact (continuous_iff_continuousAt.mpr (fun t =>
        (GammaPhaseApproximation.phase_hasDerivAt (by norm_num : (0 : ℝ) < 1 / 4) t).continuousAt)).comp (by fun_prop)
    · fun_prop
  · rw [continuous_iff_continuousAt]
    intro T
    exact (differentiableAt_riemannZeta (point_ne_one T)).continuousAt.comp
      (by unfold point; fun_prop : ContinuousAt point T)

/-- The finite approximation rotates actual zeta using only elementary terms. -/
def approximateHardy (T : ℝ) : ℝ :=
  (Complex.exp (I * GammaPhaseApproximation.thetaApproximation 200 T) *
    riemannZeta (point T)).re

/-- The finite phase error changes the Hardy value by one exact real cosine. -/
theorem approximateHardy_eq (T : ℝ) :
    approximateHardy T = hardy T * Real.cos
      (GammaPhaseApproximation.thetaApproximation 200 T - GammaPhaseApproximation.theta T) := by
  have he : Complex.exp (I * GammaPhaseApproximation.thetaApproximation 200 T) *
      riemannZeta (point T) = (hardy T : ℂ) * Complex.exp (I *
        (GammaPhaseApproximation.thetaApproximation 200 T - GammaPhaseApproximation.theta T)) := by
    rw [hardy_ofReal]
    calc
      _ = (Complex.exp (I * GammaPhaseApproximation.theta T) *
          Complex.exp (I * (GammaPhaseApproximation.thetaApproximation 200 T -
            GammaPhaseApproximation.theta T))) * riemannZeta (point T) := by
        rw [← Complex.exp_add]
        congr 2
        ring
      _ = _ := by ring
  unfold approximateHardy
  rw [he]
  simp [Complex.exp_re, mul_comm]

/-- The finite approximation retains more than `97/98` of the real Hardy
amplitude throughout the required height range. -/
theorem cosine_error_gt {T : ℝ} (hT : |T| ≤ 22000) :
    97 / 98 < Real.cos (GammaPhaseApproximation.thetaApproximation 200 T -
      GammaPhaseApproximation.theta T) := by
  have hh := GammaPhaseApproximation.theta_error_lt_one_seventh hT
  rw [abs_sub_comm] at hh
  let d := GammaPhaseApproximation.thetaApproximation 200 T - GammaPhaseApproximation.theta T
  have hd : |d| < 1 / 7 := hh
  have hsq := mul_self_lt_mul_self (abs_nonneg d) hd
  have hcos := Real.one_sub_sq_div_two_le_cos (x := d)
  nlinarith [sq_abs d]

/-- The cosine loss is strictly positive, so the finite phase approximation
cannot reverse the actual Hardy sign. -/
theorem cosine_error_pos {T : ℝ} (hT : |T| ≤ 22000) :
    0 < Real.cos (GammaPhaseApproximation.thetaApproximation 200 T -
      GammaPhaseApproximation.theta T) :=
  lt_trans (by norm_num) (cosine_error_gt hT)

/-- Positive signs of the finite rotated computation certify actual Hardy signs. -/
theorem approximateHardy_pos_iff {T : ℝ} (hT : |T| ≤ 22000) :
    0 < approximateHardy T ↔ 0 < hardy T := by
  rw [approximateHardy_eq, mul_pos_iff_of_pos_right (cosine_error_pos hT)]

/-- Negative signs of the finite rotated computation certify actual Hardy signs. -/
theorem approximateHardy_neg_iff {T : ℝ} (hT : |T| ≤ 22000) :
    approximateHardy T < 0 ↔ hardy T < 0 := by
  rw [approximateHardy_eq]
  simpa only [zero_mul] using
    (mul_lt_mul_iff_left₀ (b := hardy T) (c := 0) (cosine_error_pos hT))

/-- Two rigorously checked opposite signs of the finite-phase rotation imply
an actual critical-line zero between the heights. This is a lower-count tool;
it does not assert the interval contains only one zero. -/
theorem exists_zero_of_approximate_sign_change {a b : ℝ} (hab : a ≤ b)
    (ha : |a| ≤ 22000) (hb : |b| ≤ 22000)
    (hleft : approximateHardy a < 0) (hright : 0 < approximateHardy b) :
    ∃ t ∈ Ioo a b, riemannZeta (point t) = 0 := by
  have hl := (approximateHardy_neg_iff ha).mp hleft
  have hr := (approximateHardy_pos_iff hb).mp hright
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Ioo hab continuous_hardy.continuousOn ⟨hl, hr⟩
  exact ⟨t, ht, (hardy_eq_zero_iff t).mp hzero⟩

/-- Either orientation of a checked sign change gives a critical-line zero.
The sign product is a finite numerical target, not an assumed zero count. -/
theorem exists_zero_of_approximate_mul_neg {a b : ℝ} (hab : a ≤ b)
    (ha : |a| ≤ 22000) (hb : |b| ≤ 22000)
    (hsign : approximateHardy a * approximateHardy b < 0) :
    ∃ t ∈ Ioo a b, riemannZeta (point t) = 0 := by
  rcases mul_neg_iff.mp hsign with h | h
  · have hl := (approximateHardy_pos_iff ha).mp h.1
    have hr := (approximateHardy_neg_iff hb).mp h.2
    obtain ⟨t, ht, hzero⟩ := intermediate_value_Ioo' hab continuous_hardy.continuousOn ⟨hr, hl⟩
    exact ⟨t, ht, (hardy_eq_zero_iff t).mp hzero⟩
  · exact exists_zero_of_approximate_sign_change hab ha hb h.1 h.2

end
end RiemannGaussian.ZetaHardyPhase
