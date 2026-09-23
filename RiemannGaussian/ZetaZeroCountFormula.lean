/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaCountingPoles
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Complete zero counting with an explicit Gamma-phase error

The actual symmetric multiplicity count is the sum of the two evaluated
pole terms, the unwrapped theta phase, and the genuine zeta boundary phase.
The finite theta approximation changes that complete count expression by
less than one tenth through height 22000. The zeta boundary phase still
needs numerical certification; it is not assumed small.
-/

namespace RiemannGaussian.ZetaZeroCountFormula
noncomputable section
open Complex MeasureTheory Set
open GammaCountingPhase ZetaCountingPoles
open scoped Interval

private theorem vertical_ne_one (t : ℝ) : (3 / 2 : ℂ) + t * I ≠ 1 := by
  intro he
  have hh := congrArg Complex.re he
  norm_num at hh

private theorem horizontal_ne_one {T : ℝ} (hT : T ≠ 0) (x : ℝ) : (x : ℂ) + T * I ≠ 1 := by
  intro he
  apply hT
  simpa using congrArg Complex.im he

/-- A regular zero height makes the actual positive-real-part horizontal
zeta segment nonvanishing. This follows from the complete xi divisor. -/
theorem zeta_horizontal_ne_zero {T : ℝ} (hT : 0 < T)
    (hb : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T) {x : ℝ} (hx : 0 < x) :
    riemannZeta ((x : ℂ) + T * I) ≠ 0 := by
  intro hz
  have hxi := riemannXiSpectral_ne_zero_of_abs_re_ne
    (by simpa only [zetaSpectralCoordinate_re] using hb)
    (z := zetaSpectralCoordinate ((x : ℂ) + T * I))
    (by simpa using abs_of_pos hT)
  apply hxi
  rw [riemannXiSpectral, completedSpectralCoordinate_zetaSpectralCoordinate,
    riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos (by simpa using hx)
      (horizontal_ne_one hT.ne' x), hz, mul_zero]

private theorem analytic_zeta_log {s : ℂ} (hs : s ≠ 1) (hn : riemannZeta s ≠ 0) :
    AnalyticAt ℂ (logDeriv riemannZeta) s := by
  have hh := analyticOn_riemannZeta s hs
  simpa only [logDeriv] using hh.deriv.div hh hn

/-- Actual zeta's logarithmic derivative is integrable along the safe right line. -/
theorem zeta_vertical_integrable (T : ℝ) :
    IntervalIntegrable (fun t : ℝ => logDeriv riemannZeta ((3 / 2 : ℂ) + t * I)) volume 0 T := by
  apply Continuous.intervalIntegrable
  apply continuous_comp_of_forall_analyticAt _ _ (by fun_prop)
  intro t
  apply analytic_zeta_log (vertical_ne_one t)
  apply riemannZeta_ne_zero_of_one_le_re
  norm_num

/-- Actual zeta's logarithmic derivative is integrable along the whole
horizontal path at a positive regular height. -/
theorem zeta_horizontal_integrable {T : ℝ} (hT : 0 < T)
    (hb : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T) :
    IntervalIntegrable (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + T * I))
      volume (1 / 2 : ℝ) (3 / 2) := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx' : 0 < x := by
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] at hx
    linarith [hx.1]
  exact ((analytic_zeta_log (horizontal_ne_one hT.ne' x)
    (zeta_horizontal_ne_zero hT hb hx')).continuousAt.comp (f := fun y : ℝ => (y : ℂ) + T * I)
    (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + T * I) x)).continuousWithinAt

private theorem completed_split {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = poles s + logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  rw [logDeriv_riemannXi_of_re_pos_of_riemannZeta_ne_zero hs h1 hz, logDeriv_Gammaℝ hs]
  simp only [poles, pole, ofReal_zero, sub_zero, ofReal_one, one_div]
  ring

/-- The entire xi path splits into the actual pole, Gamma and zeta phases,
with every integrability obligation discharged on the complete segments. -/
theorem xi_path_split {T : ℝ} (hT : 0 < T)
    (hb : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T) :
    pathPhase (logDeriv riemannXi) T =
      Real.pi + GammaPhaseApproximation.theta T + pathPhase (logDeriv riemannZeta) T := by
  have he : pathPhase (logDeriv riemannXi) T =
      pathPhase (fun s => poles s + logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s) T := by
    unfold pathPhase
    congr 1
    · apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [completed_split (by norm_num) (vertical_ne_one t)
        (riemannZeta_ne_zero_of_one_le_re (by norm_num))]
    · apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      have hx' : 0 < x := by
        rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] at hx
        linarith [hx.1]
      rw [completed_split (by simpa using hx') (horizontal_ne_one hT.ne' x)
        (zeta_horizontal_ne_zero hT hb hx')]
  have hgv : IntervalIntegrable (fun t : ℝ => logDeriv Complex.Gammaℝ ((3 / 2 : ℂ) + t * I))
      volume 0 T := by simpa using gamma_vertical_integrable (by norm_num : (0 : ℝ) < 3 / 2) T
  rw [he, pathPhase_add T ((poles_vertical_integrable T).add hgv)
    ((poles_horizontal_integrable hT.ne').add (gamma_horizontal_integrable T))
    (zeta_vertical_integrable T) (zeta_horizontal_integrable hT hb),
    pathPhase_add T (poles_vertical_integrable T) (poles_horizontal_integrable hT.ne')
      hgv (gamma_horizontal_integrable T), poles_path hT, gamma_path_eq_theta]

/-- The complete symmetric zero count, with genuine multiplicities, has
the exact classical phase formula. The zeta phase is retained in full. -/
theorem count_formula {T : ℝ} (hT : 0 < T)
    (hb : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T) :
    (ZetaFiniteZeroCount.count T : ℝ) = 2 + (2 / Real.pi) *
      (GammaPhaseApproximation.theta T + pathPhase (logDeriv riemannZeta) T) := by
  have hh := count_eq_pathPhase hT.le hb
  rw [xi_path_split hT hb] at hh
  field_simp
  nlinarith

/-- The finite Gamma expression together with the unchanged actual zeta
boundary phase. No numerical bound for that phase is built into this definition. -/
def approximateCount (T : ℝ) : ℝ := 2 + (2 / Real.pi) *
  (GammaPhaseApproximation.thetaApproximation 200 T + pathPhase (logDeriv riemannZeta) T)

/-- Replacing only Gamma by its explicit finite formula costs less than
one tenth of a zero in the complete symmetric count throughout the required
height range. The entire zeta phase cancels in the error comparison. -/
theorem count_error_lt_one_tenth {T : ℝ} (hT : 0 < T) (hH : T ≤ 22000)
    (hb : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T) :
    |(ZetaFiniteZeroCount.count T : ℝ) - approximateCount T| < 1 / 10 := by
  rw [count_formula hT hb]
  have he : 2 + 2 / Real.pi * (GammaPhaseApproximation.theta T + pathPhase (logDeriv riemannZeta) T) -
      approximateCount T = 2 / Real.pi *
        (GammaPhaseApproximation.theta T - GammaPhaseApproximation.thetaApproximation 200 T) := by
    unfold approximateCount
    ring
  rw [he, abs_mul, abs_of_pos (div_pos (by norm_num) Real.pi_pos)]
  have hh := GammaPhaseApproximation.theta_error_lt_one_seventh (T := T)
    (by simpa only [abs_of_pos hT] using hH)
  calc
    _ < (2 / Real.pi) * (1 / 7) := mul_lt_mul_of_pos_left hh (by positivity)
    _ < 1 / 10 := by
      have hp := Real.pi_gt_three
      field_simp
      linarith

/-- A concrete numerical enclosure within nine tenths of an integer is
sufficient to certify the complete multiplicity count. The numerical
enclosure remains an explicit obligation, not a presumed computation. -/
theorem count_eq_of_approximation {T : ℝ} (hT : 0 < T) (hH : T ≤ 22000)
    (hb : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T) (m : ℕ)
    (hm : |approximateCount T - m| ≤ 9 / 10) : ZetaFiniteZeroCount.count T = m := by
  have he := count_error_lt_one_tenth hT hH hb
  have hh : |(ZetaFiniteZeroCount.count T : ℝ) - m| < 1 := by
    calc
      _ = |((ZetaFiniteZeroCount.count T : ℝ) - approximateCount T) +
          (approximateCount T - m)| := by congr 1; ring
      _ ≤ |(ZetaFiniteZeroCount.count T : ℝ) - approximateCount T| +
          |approximateCount T - m| := abs_add_le _ _
      _ < 1 := by linarith
  have hlt := abs_lt.mp hh
  have h1 : ZetaFiniteZeroCount.count T < m + 1 := by exact_mod_cast (by linarith :
    (ZetaFiniteZeroCount.count T : ℝ) < (m : ℝ) + 1)
  have h2 : m < ZetaFiniteZeroCount.count T + 1 := by exact_mod_cast (by linarith :
    (m : ℝ) < (ZetaFiniteZeroCount.count T : ℝ) + 1)
  omega

end
end RiemannGaussian.ZetaZeroCountFormula
