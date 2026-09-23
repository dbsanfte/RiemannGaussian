/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogPrimeSeries
import RiemannGaussian.ZetaStripPhaseFamily
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The right counting line stays in the positive zeta half-plane

The complete logarithmic Euler series has norm at most the positive real
logarithmic mass. At abscissa 3/2 that mass is at most log 3, strictly below
pi/2. Consequently actual zeta has positive real part at every height on
the counting line, so its principal logarithm loses no winding there.
-/

namespace RiemannGaussian.ZetaRightPhase
noncomputable section
open Complex

/-- The norm of every logarithmic Euler term is its original positive weight. -/
theorem norm_log_term (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term (fun m => (ZetaLogPrimeSeries.coefficient m : ℂ)) ((σ : ℂ) + I * t) n‖ =
      ZetaLogPrimeSeries.weight σ n := by
  rw [ZetaLogPrimeSeries.term_eq_phase, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (ZetaLogPrimeSeries.weight_nonneg σ n), Complex.norm_exp]
  simp only [neg_re, mul_re, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, sub_zero, neg_zero, Real.exp_zero, mul_one]

/-- The complete complex logarithmic Euler series has a uniform norm bound,
retaining the original positive prime-power mass. -/
theorem norm_log_series_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖LSeries (fun m => (ZetaLogPrimeSeries.coefficient m : ℂ)) ((σ : ℂ) + I * t)‖ ≤
      Real.log ‖riemannZeta (σ : ℂ)‖ := by
  have hs := ZetaLogPrimeSeries.summable_series (s := (σ : ℂ) + I * t) (by simpa using hσ)
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun m => (ZetaLogPrimeSeries.coefficient m : ℂ))
        ((σ : ℂ) + I * t) n‖ := norm_tsum_le_tsum_norm hs.norm
    _ = _ := by
      simp_rw [norm_log_term]
      exact (ZetaLogPrimeSeries.hasSum_weight hσ).tsum_eq

/-- The entire unwrapped Euler logarithm is smaller than `pi/2` on the
safe counting line, uniformly over all real ordinates. -/
theorem norm_safe_log_lt (t : ℝ) :
    ‖LSeries (fun m => (ZetaLogPrimeSeries.coefficient m : ℂ)) ((3 / 2 : ℂ) + I * t)‖ < Real.pi / 2 := by
  have hh := norm_log_series_le (by norm_num : (1 : ℝ) < 3 / 2) t
  have hz := ZetaStripPhaseFamily.log_norm_zeta_le_euler (s := (3 / 2 : ℂ)) (by norm_num)
  norm_num at hh hz
  have hlog := Real.log_three_lt_d9
  have hp := Real.pi_gt_three
  linarith

/-- Actual zeta stays strictly in the positive real half-plane on the
entire right counting line. No finite-height or zero hypothesis is needed. -/
theorem zeta_re_pos (t : ℝ) : 0 < (riemannZeta ((3 / 2 : ℂ) + t * I)).re := by
  have he := ZetaLogPrimeSeries.exp_series_eq (s := (3 / 2 : ℂ) + I * t) (by norm_num)
  rw [show (3 / 2 : ℂ) + t * I = (3 / 2 : ℂ) + I * t by ring, ← he, Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  exact abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt (norm_safe_log_lt t))

end
end RiemannGaussian.ZetaRightPhase
